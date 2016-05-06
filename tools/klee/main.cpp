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

  cl::list<std::string>
  InputArgv(cl::ConsumeAfter, cl::desc("<program arguments>..."));

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
  unsigned m_testIndex;  // number of tests written so far
  unsigned m_pathsExplored; // number of paths explored so far
public:
  KleeHandler();
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

KleeHandler::KleeHandler()
  : m_interpreter(0),
    m_pathWriter(0),
    m_symPathWriter(0),
    m_infoFile(0),
    m_testIndex(0),
    m_pathsExplored(0) {
  klee_warning_file = stdout;
  klee_message_file = stdout;
  m_infoFile = openOutputFile("info");
}

KleeHandler::~KleeHandler() {
  if (m_pathWriter) delete m_pathWriter;
  if (m_symPathWriter) delete m_symPathWriter;
  delete m_infoFile;
}

void KleeHandler::setInterpreter(Interpreter *i) {
  m_interpreter = i;

  if (1) {
    m_pathWriter = new TreeStreamWriter(getOutputFilename("paths.ts"));
    assert(m_pathWriter->good());
    m_interpreter->setPathWriter(m_pathWriter);
  }

  if (1) {
    m_symPathWriter = new TreeStreamWriter(getOutputFilename("symPaths.ts"));
    assert(m_symPathWriter->good());
    m_interpreter->setSymbolicPathWriter(m_symPathWriter);
  }
}

std::string KleeHandler::getOutputFilename(const std::string &filename) {
  return "tmp/" + filename;
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
void KleeHandler::processTestCase(const ExecutionState &state, const char *errorMessage, const char *errorSuffix)
{
printf("[%s:%d] start\n", __FUNCTION__, __LINE__);
  std::vector< std::pair<std::string, std::vector<unsigned char> > > out;
  bool success = m_interpreter->getSymbolicSolution(state, out);

    if (!success)
      klee_warning("unable to get symbolic solution, losing test case");
    unsigned id = ++m_testIndex;
printf("[%s:%d] outsize %d\n", __FUNCTION__, __LINE__, (int)out.size());
    for (unsigned i=0; i<out.size(); i++)
       printf("[%s:%d] [%d] = '%s'\n", __FUNCTION__, __LINE__, i, const_cast<char*>(out[i].first.c_str()));
    if (errorMessage) {
       llvm::outs() << "TESTERROR:\n" << errorMessage << "\n";
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
    if (errorMessage || 1) {
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints,Interpreter::KQUERY);
      llvm::raw_ostream *f = openTestFile("pc", id);
      *f << constraints;
      delete f;
    }
    if (1) {
      // FIXME: If using Z3 as the core solver the emitted file is actually
      // SMT-LIBv2 not CVC which is a bit confusing
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints, Interpreter::STP);
      llvm::raw_ostream *f = openTestFile("cvc", id);
      *f << constraints;
      delete f;
    }
    if(1) {
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
    if (1) {
      std::map<const std::string*, std::set<unsigned> > cov;
      m_interpreter->getCoveredLines(state, cov);
      llvm::raw_ostream *f = openTestFile("cov", id);
      for (std::map<const std::string*, std::set<unsigned> >::iterator it = cov.begin(), ie = cov.end(); it != ie; ++it) {
        for (std::set<unsigned>::iterator it2 = it->second.begin(), ie = it->second.end(); it2 != ie; ++it2)
          *f << *it->first << ":" << *it2 << "\n";
      }
      delete f;
    }
printf("[%s:%d] end\n", __FUNCTION__, __LINE__);
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
static void parseArguments(int argc, char **argv)
{ 
  cl::SetVersionPrinter(klee::printVersion); 
  cl::ParseCommandLineOptions(argc, (char **)argv, " klee\n"); // removes // warning
}

int main(int argc, char **argv, char **envp)
{
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
  Interpreter::ModuleOptions Opts(LibraryDir.c_str(), OptimizeModule, CheckDivZero, CheckOvershift); 

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
    llvm::outs() << "'" << "main" << "' function not found in module.\n";
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
  KleeHandler *handler = new KleeHandler();
printf("[%s:%d] create Interpreter\n", __FUNCTION__, __LINE__);
  Interpreter *interpreter = Interpreter::create(IOpts, handler);
  handler->setInterpreter(interpreter);
  const Module *finalModule = interpreter->setModule(mainModule, Opts);

printf("[%s:%d] before runFunctionAsMain\n", __FUNCTION__, __LINE__);
  interpreter->runFunctionAsMain(mainFn, pArgc, pArgv, pEnvp);
printf("[%s:%d] after runFunctionAsMain\n", __FUNCTION__, __LINE__);

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
