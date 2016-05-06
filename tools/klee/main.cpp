/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/Statistics.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Support/ErrorHandling.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"

#include <dirent.h>
#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>

#include <cerrno>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <sstream>


using namespace llvm;
using namespace klee;

namespace {
  cl::opt<std::string>
  InputFile(cl::desc("<input bytecode>"), cl::Positional, cl::init("-"));

  cl::opt<std::string>
  RunInDir("run-in", cl::desc("Change to the given directory prior to executing"));

  cl::list<std::string>
  InputArgv(cl::ConsumeAfter, cl::desc("<program arguments>..."));

  cl::opt<bool>
  NoOutput("no-output", cl::desc("Don't generate test files"));

  cl::opt<bool>
  WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));

  cl::opt<bool>
  WriteCVCs("write-cvcs", cl::desc("Write .cvc files for each test case"));

  cl::opt<bool>
  WritePCs("write-pcs", cl::desc("Write .pc files for each test case"));

  cl::opt<bool>
  WriteSMT2s("write-smt2s", cl::desc("Write .smt2 (SMT-LIBv2) files for each test case"));

  cl::opt<bool>
  WriteCov("write-cov", cl::desc("Write coverage information for each test case"));

  cl::opt<bool>
  WriteTestInfo("write-test-info", cl::desc("Write additional test case information"));

  cl::opt<bool>
  WritePaths("write-paths", cl::desc("Write .path files for each test case"));

  cl::opt<bool>
  WriteSymPaths("write-sym-paths", cl::desc("Write .sym.path files for each test case"));

  cl::opt<bool>
  ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));

  cl::opt<bool>
  OptimizeModule("optimize", cl::desc("Optimize before execution"), cl::init(false));

  cl::opt<bool>
  CheckDivZero("check-div-zero", cl::desc("Inject checks for division-by-zero"), cl::init(true));

  cl::opt<bool>
  CheckOvershift("check-overshift", cl::desc("Inject checks for overshift"), cl::init(true));

  cl::list<std::string>
  LinkLibraries("link-llvm-lib", cl::desc("Link the given libraries before execution"), cl::value_desc("library file"));

  cl::opt<unsigned>
  MakeConcreteSymbolic("make-concrete-symbolic", cl::desc("Probabilistic rate at which to make concrete reads symbolic, " "i.e. approximately 1 in n concrete reads will be made symbolic (0=off, 1=all).  " "Used for testing."), cl::init(0));
}

/***/

class KleeHandler : public InterpreterHandler {
private:
  Interpreter *m_interpreter;
  TreeStreamWriter *m_pathWriter, *m_symPathWriter;
  llvm::raw_ostream *m_infoFile; 
  SmallString<128> m_outputDirectory; 
  unsigned m_testIndex;  // number of tests written so far
  unsigned m_pathsExplored; // number of paths explored so far

  // used for writing .ktest files
  int m_argc;
  char **m_argv;

public:
  KleeHandler(int argc, char **argv);
  ~KleeHandler();

  llvm::raw_ostream &getInfoStream() const { return *m_infoFile; }
  void incPathsExplored() { m_pathsExplored++; }

  void setInterpreter(Interpreter *i);

  void processTestCase(const ExecutionState  &state, const char *errorMessage, const char *errorSuffix); 
  std::string getOutputFilename(const std::string &filename);
  llvm::raw_fd_ostream *openOutputFile(const std::string &filename);
  std::string getTestFilename(const std::string &suffix, unsigned id);
  llvm::raw_fd_ostream *openTestFile(const std::string &suffix, unsigned id);

  static std::string getRunTimeLibraryPath(const char *argv0);
};

KleeHandler::KleeHandler(int argc, char **argv)
  : m_interpreter(0),
    m_pathWriter(0),
    m_symPathWriter(0),
    m_infoFile(0),
    m_outputDirectory(),
    m_testIndex(0),
    m_pathsExplored(0),
    m_argc(argc),
    m_argv(argv) {
  SmallString<128> directory(InputFile);

  sys::path::remove_filename(directory);
  if (auto ec = sys::fs::make_absolute(directory)) {
    klee_error("unable to determine absolute path: %s", ec.message().c_str());
  }
    // "klee-out-<i>"
    int i = 0;
    for (; i <= INT_MAX; ++i) {
      SmallString<128> d(directory);
      llvm::sys::path::append(d, "klee-out-");
      raw_svector_ostream ds(d); ds << i; ds.flush();

      // create directory and try to link klee-last
      if (mkdir(d.c_str(), 0775) == 0) {
        m_outputDirectory = d; 
        SmallString<128> klee_last(directory);
        llvm::sys::path::append(klee_last, "klee-last"); 
        if (((unlink(klee_last.c_str()) < 0) && (errno != ENOENT)) ||
            symlink(m_outputDirectory.c_str(), klee_last.c_str()) < 0) { 
          klee_warning("cannot create klee-last symlink: %s", strerror(errno));
        } 
        break;
      } 
      // otherwise try again or exit on error
      if (errno != EEXIST)
        klee_error("cannot create \"%s\": %s", m_outputDirectory.c_str(), strerror(errno));
    }
    if (i == INT_MAX && m_outputDirectory.str().equals(""))
        klee_error("cannot create output directory: index out of range");

  klee_message("output directory is \"%s\"", m_outputDirectory.c_str());

  // open warnings.txt
  std::string file_path = getOutputFilename("warnings.txt");
  if ((klee_warning_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno)); 
  // open messages.txt
  file_path = getOutputFilename("messages.txt");
  if ((klee_message_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno)); 
  // open info
  m_infoFile = openOutputFile("info");
}

KleeHandler::~KleeHandler() {
  if (m_pathWriter) delete m_pathWriter;
  if (m_symPathWriter) delete m_symPathWriter;
  fclose(klee_warning_file);
  fclose(klee_message_file);
  delete m_infoFile;
}

void KleeHandler::setInterpreter(Interpreter *i) {
  m_interpreter = i;

  if (WritePaths) {
    m_pathWriter = new TreeStreamWriter(getOutputFilename("paths.ts"));
    assert(m_pathWriter->good());
    m_interpreter->setPathWriter(m_pathWriter);
  }

  if (WriteSymPaths) {
    m_symPathWriter = new TreeStreamWriter(getOutputFilename("symPaths.ts"));
    assert(m_symPathWriter->good());
    m_interpreter->setSymbolicPathWriter(m_symPathWriter);
  }
}

std::string KleeHandler::getOutputFilename(const std::string &filename) {
  SmallString<128> path = m_outputDirectory;
  sys::path::append(path,filename);
  return path.str();
}

llvm::raw_fd_ostream *KleeHandler::openOutputFile(const std::string &filename) {
  llvm::raw_fd_ostream *f;
  std::string Error;
  std::string path = getOutputFilename(filename);
  std::error_code ec;
  f = new llvm::raw_fd_ostream(path.c_str(), ec, llvm::sys::fs::F_None);
  if (ec)
    Error = ec.message();
  if (!Error.empty()) {
    klee_error("error opening file \"%s\".  KLEE may have run out of file " "descriptors: try to increase the maximum number of open file " "descriptors by using ulimit (%s).", filename.c_str(), Error.c_str());
    delete f;
    f = NULL;
  }

  return f;
}

std::string KleeHandler::getTestFilename(const std::string &suffix, unsigned id) {
  std::stringstream filename;
  filename << "test" << std::setfill('0') << std::setw(6) << id << '.' << suffix;
  return filename.str();
}

llvm::raw_fd_ostream *KleeHandler::openTestFile(const std::string &suffix, unsigned id) {
  return openOutputFile(getTestFilename(suffix, id));
}

/* Outputs all files (.ktest, .pc, .cov etc.) describing a test case */
void KleeHandler::processTestCase(const ExecutionState &state, const char *errorMessage, const char *errorSuffix) {
  if (errorMessage && ExitOnError) {
    llvm::errs() << "EXITING ON ERROR:\n" << errorMessage << "\n";
    exit(1);
  }

  if (!NoOutput) {
    std::vector< std::pair<std::string, std::vector<unsigned char> > > out;
    bool success = m_interpreter->getSymbolicSolution(state, out);

    if (!success)
      klee_warning("unable to get symbolic solution, losing test case");

    double start_time = util::getWallTime();

    unsigned id = ++m_testIndex;

    if (success) {
      KTest b;
      b.numArgs = m_argc;
      b.args = m_argv;
      b.symArgvs = 0;
      b.symArgvLen = 0;
      b.numObjects = out.size();
      b.objects = new KTestObject[b.numObjects];
      assert(b.objects);
      for (unsigned i=0; i<b.numObjects; i++) {
        KTestObject *o = &b.objects[i];
        o->name = const_cast<char*>(out[i].first.c_str());
        o->numBytes = out[i].second.size();
        o->bytes = new unsigned char[o->numBytes];
        assert(o->bytes);
        std::copy(out[i].second.begin(), out[i].second.end(), o->bytes);
      }

      if (!kTest_toFile(&b, getOutputFilename(getTestFilename("ktest", id)).c_str())) {
        klee_warning("unable to write output test case, losing it");
      }

      for (unsigned i=0; i<b.numObjects; i++)
        delete[] b.objects[i].bytes;
      delete[] b.objects;
    }

    if (errorMessage) {
      llvm::raw_ostream *f = openTestFile(errorSuffix, id);
      *f << errorMessage;
      delete f;
    }

    if (m_pathWriter) {
      std::vector<unsigned char> concreteBranches;
      m_pathWriter->readStream(m_interpreter->getPathStreamID(state), concreteBranches);
      llvm::raw_fd_ostream *f = openTestFile("path", id);
      for (std::vector<unsigned char>::iterator I = concreteBranches.begin(), E = concreteBranches.end(); I != E; ++I) {
        *f << *I << "\n";
      }
      delete f;
    }

    if (errorMessage || WritePCs) {
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints,Interpreter::KQUERY);
      llvm::raw_ostream *f = openTestFile("pc", id);
      *f << constraints;
      delete f;
    }

    if (WriteCVCs) {
      // FIXME: If using Z3 as the core solver the emitted file is actually
      // SMT-LIBv2 not CVC which is a bit confusing
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints, Interpreter::STP);
      llvm::raw_ostream *f = openTestFile("cvc", id);
      *f << constraints;
      delete f;
    }

    if(WriteSMT2s) {
      std::string constraints;
        m_interpreter->getConstraintLog(state, constraints, Interpreter::SMTLIB2);
        llvm::raw_ostream *f = openTestFile("smt2", id);
        *f << constraints;
        delete f;
    }

    if (m_symPathWriter) {
      std::vector<unsigned char> symbolicBranches;
      m_symPathWriter->readStream(m_interpreter->getSymbolicPathStreamID(state), symbolicBranches);
      llvm::raw_fd_ostream *f = openTestFile("sym.path", id);
      for (std::vector<unsigned char>::iterator I = symbolicBranches.begin(), E = symbolicBranches.end(); I!=E; ++I) {
        *f << *I << "\n";
      }
      delete f;
    }

    if (WriteCov) {
      std::map<const std::string*, std::set<unsigned> > cov;
      m_interpreter->getCoveredLines(state, cov);
      llvm::raw_ostream *f = openTestFile("cov", id);
      for (std::map<const std::string*, std::set<unsigned> >::iterator it = cov.begin(), ie = cov.end(); it != ie; ++it) {
        for (std::set<unsigned>::iterator it2 = it->second.begin(), ie = it->second.end(); it2 != ie; ++it2)
          *f << *it->first << ":" << *it2 << "\n";
      }
      delete f;
    }

    if (WriteTestInfo) {
      double elapsed_time = util::getWallTime() - start_time;
      llvm::raw_ostream *f = openTestFile("info", id);
      *f << "Time to generate test case: " << elapsed_time << "s\n";
      delete f;
    }
  }
}

std::string KleeHandler::getRunTimeLibraryPath(const char *argv0) {
  // Take any function from the execution binary but not main (as not allowed by // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot( llvm::sys::fs::getMainExecutable(argv0, MainExecAddr)); 
  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot); 
  SmallString<128> libDir; 
  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() << "Using build directory KLEE library runtime :");
  libDir = KLEE_DIR;
  llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
  llvm::sys::path::append(libDir,"lib"); 
  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() << libDir.c_str() << "\n");
  return libDir.str();
}

//===----------------------------------------------------------------------===//
// main Driver function
//
static void parseArguments(int argc, char **argv) { 
  cl::SetVersionPrinter(klee::printVersion); 
  cl::ParseCommandLineOptions(argc, (char **)argv, " klee\n"); // removes // warning
}

// returns the end of the string put in buf
static char *format_tdiff(char *buf, long seconds)
{
  assert(seconds >= 0);

  long minutes = seconds / 60;  seconds %= 60;
  long hours   = minutes / 60;  minutes %= 60;
  long days    = hours   / 24;  hours   %= 24;

  buf = strrchr(buf, '\0');
  if (days > 0) buf += sprintf(buf, "%ld days, ", days);
  buf += sprintf(buf, "%02ld:%02ld:%02ld", hours, minutes, seconds);
  return buf;
}

int main(int argc, char **argv, char **envp) {
printf("[%s:%d]klee: ", __FUNCTION__, __LINE__);
for (int i = 0; i < argc; i++)
    printf("; %s", argv[i]);
printf("\n");
  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.

  llvm::InitializeNativeTarget();
  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();

  // Load the bytecode...
  std::string ErrorMsg;
  Module *mainModule = 0;
  auto Buffer = MemoryBuffer::getFileOrSTDIN(InputFile.c_str());
  if (!Buffer)
    klee_error("error loading program '%s': %s", InputFile.c_str(), Buffer.getError().message().c_str());
  auto mainModuleOrError = getLazyBitcodeModule(std::move(Buffer.get()), getGlobalContext());
  if (!mainModuleOrError) {
    klee_error("error loading program '%s': %s", InputFile.c_str(), mainModuleOrError.getError().message().c_str());
  }
  // The module has taken ownership of the MemoryBuffer so release it from the std::unique_ptr
  Buffer->release();
  mainModule = mainModuleOrError->release();
  if (auto ec = mainModule->materializeAllPermanently()) {
    klee_error("error loading program '%s': %s", InputFile.c_str(), ec.message().c_str());
  }

  std::string LibraryDir = KleeHandler::getRunTimeLibraryPath(argv[0]);
  Interpreter::ModuleOptions Opts(LibraryDir.c_str(), /*Optimize=*/OptimizeModule, /*CheckDivZero=*/CheckDivZero, /*CheckOvershift=*/CheckOvershift); 

  std::vector<std::string>::iterator libs_it;
  std::vector<std::string>::iterator libs_ie;
  for (libs_it = LinkLibraries.begin(), libs_ie = LinkLibraries.end(); libs_it != libs_ie; ++libs_it) {
    const char * libFilename = libs_it->c_str();
    klee_message("Linking in library: %s.\n", libFilename);
    mainModule = klee::linkWithLibrary(mainModule, libFilename);
  }
  // Get the desired main function.  klee_main initializes uClibc
  // locale and other data and then calls main.
  Function *mainFn = mainModule->getFunction("main");
  if (!mainFn) {
    llvm::errs() << "'" << "main" << "' function not found in module.\n";
    return -1;
  }

  // FIXME: Change me to std types.
  int pArgc = InputArgv.size() + 1;
  char **pArgv = new char *[pArgc];
  char **pEnvp = envp;

  for (unsigned i=0; i<InputArgv.size()+1; i++) {
    std::string &arg = (i==0 ? InputFile : InputArgv[i-1]);
    unsigned size = arg.size() + 1;
    char *pArg = new char[size]; 
    std::copy(arg.begin(), arg.end(), pArg);
    pArg[size - 1] = 0; 
    pArgv[i] = pArg;
  } 
  Interpreter::InterpreterOptions IOpts;
  IOpts.MakeConcreteSymbolic = MakeConcreteSymbolic;
  KleeHandler *handler = new KleeHandler(pArgc, pArgv);
printf("[%s:%d] create Interpreter\n", __FUNCTION__, __LINE__);
  Interpreter *interpreter = Interpreter::create(IOpts, handler);
  handler->setInterpreter(interpreter);

  for (int i=0; i<argc; i++) {
    llvm::outs() << argv[i] << (i+1<argc ? " ":"\n");
  }
  llvm::outs() << "PID: " << getpid() << "\n"; 
  const Module *finalModule = interpreter->setModule(mainModule, Opts);

  char buf[256];
  time_t t[2];
  t[0] = time(NULL);
  strftime(buf, sizeof(buf), "Started: %Y-%m-%d %H:%M:%S\n", localtime(&t[0]));
  llvm::outs() << buf;

printf("[%s:%d] before runFunctionAsMain\n", __FUNCTION__, __LINE__);
  interpreter->runFunctionAsMain(mainFn, pArgc, pArgv, pEnvp);
printf("[%s:%d] after runFunctionAsMain\n", __FUNCTION__, __LINE__);

  t[1] = time(NULL);
  strftime(buf, sizeof(buf), "Finished: %Y-%m-%d %H:%M:%S\n", localtime(&t[1]));
  llvm::outs() << buf;

  strcpy(buf, "Elapsed: ");
  strcpy(format_tdiff(buf, t[1] - t[0]), "\n");
  llvm::outs() << buf;

  // Free all the args.
  for (unsigned i=0; i<InputArgv.size()+1; i++)
    delete[] pArgv[i];
  delete[] pArgv;

  delete interpreter;

  uint64_t queries = *theStatisticManager->getStatisticByName("Queries");
  uint64_t queriesValid = *theStatisticManager->getStatisticByName("QueriesValid");
  uint64_t queriesInvalid = *theStatisticManager->getStatisticByName("QueriesInvalid");
  uint64_t queryCounterexamples = *theStatisticManager->getStatisticByName("QueriesCEX");
  uint64_t queryConstructs = *theStatisticManager->getStatisticByName("QueriesConstructs");
  uint64_t instructions = *theStatisticManager->getStatisticByName("Instructions");
  uint64_t forks = *theStatisticManager->getStatisticByName("Forks"); 
  llvm::outs() << "KLEE: done: explored paths = " << 1 + forks << "\n";

  // Write some extra information in the info file which users won't
  // necessarily care about or understand.
  if (queries)
    llvm::outs() << "KLEE: done: avg. constructs per query = " << queryConstructs / queries << "\n";
  llvm::outs()
    << "KLEE: done: total queries = " << queries << "\n"
    << "KLEE: done: valid queries = " << queriesValid << "\n"
    << "KLEE: done: invalid queries = " << queriesInvalid << "\n"
    << "KLEE: done: query cex = " << queryCounterexamples << "\n";

  llvm::outs() << "\n";
  llvm::outs() << "KLEE: done: total instructions = " << instructions << "\n";
  delete handler;
  return 0;
}
