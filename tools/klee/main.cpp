/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "llvm/Support/Debug.h"
#include "../lib/Core/CoreStats.h"
#include "klee/ExecutionState.h"
#include "klee/SolverStats.h"
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
  unsigned m_pathsExplored; // number of paths explored so far
public:
  KleeHandler()
    : m_interpreter(0),
      m_pathWriter(0),
      m_symPathWriter(0),
      m_infoFile(0),
      m_pathsExplored(0) {
    klee_warning_file = stdout;
    klee_message_file = stdout;
    m_infoFile = openOutputFile("info");
  }
  ~KleeHandler() {
    if (m_pathWriter) delete m_pathWriter;
    if (m_symPathWriter) delete m_symPathWriter;
    delete m_infoFile;
  }
  llvm::raw_ostream &getInfoStream() const { return *m_infoFile; }
  void incPathsExplored() { m_pathsExplored++; }
  std::string getOutputFilename(const std::string &filename) { return "tmp/" + filename; }
  void setInterpreter(Interpreter *i) {
      m_interpreter = i;
      m_pathWriter = new TreeStreamWriter(getOutputFilename("paths.ts"));
      assert(m_pathWriter->good());
      m_interpreter->setPathWriter(m_pathWriter);
      m_symPathWriter = new TreeStreamWriter(getOutputFilename("symPaths.ts"));
      assert(m_symPathWriter->good());
      m_interpreter->setSymbolicPathWriter(m_symPathWriter);
  }
  llvm::raw_fd_ostream *openOutputFile(const std::string &filename) {
    llvm::raw_fd_ostream *f;
    std::string Error;
    std::string path = getOutputFilename(filename);
    std::error_code ec;
    f = new llvm::raw_fd_ostream(path.c_str(), ec, llvm::sys::fs::F_None);
    if (ec)
      Error = ec.message();
    if (!Error.empty()) {
      klee_error("error opening file \"%s\".  (%s).", filename.c_str(), Error.c_str());
      exit(-1);
    }
    return f;
  }
  std::string getTestFilename(const std::string &suffix, unsigned id) {
    std::stringstream filename;
    filename << "test" << std::setfill('0') << std::setw(6) << id << '.' << suffix;
    return filename.str();
  }
  llvm::raw_fd_ostream *openTestFile(const std::string &suffix, unsigned id) {
    return openOutputFile(getTestFilename(suffix, id));
  }
  static std::string getRunTimeLibraryPath(const char *argv0) {
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
  void processTestCase(const ExecutionState  &state, const char *errorMessage, const char *errorSuffix); 
};

/* Outputs all files (.ktest, .pc, .cov etc.) describing a test case */
void KleeHandler::processTestCase(const ExecutionState &state, const char *errorMessage, const char *errorSuffix)
{
printf("[%s:%d] start\n", __FUNCTION__, __LINE__);
    std::vector< std::pair<std::string, std::vector<unsigned char> > > out;
    if (!m_interpreter->getSymbolicSolution(state, out))
        klee_error("unable to get symbolic solution, losing test case");
printf("[%s:%d] outsize %d\n", __FUNCTION__, __LINE__, (int)out.size());
    for (unsigned i=0; i<out.size(); i++)
        printf("[%s:%d] [%d] = '%s'\n", __FUNCTION__, __LINE__, i, const_cast<char*>(out[i].first.c_str()));
    if (errorMessage)
        llvm::outs() << "TESTERROR:\n" << errorMessage << "\n";
    if (m_pathWriter) {
printf("[%s:%d] PATH\n", __FUNCTION__, __LINE__);
      std::vector<unsigned char> concreteBranches;
      m_pathWriter->readStream(m_interpreter->getPathStreamID(state), concreteBranches);
      for (auto I = concreteBranches.begin(), E = concreteBranches.end(); I != E; ++I)
        llvm::outs() << *I << "\n";
    }
    std::string constraints;
    m_interpreter->getConstraintLog(state, constraints,Interpreter::KQUERY);
    printf("[%s:%d] KQUERY '%s'\n", __FUNCTION__, __LINE__, constraints.c_str());
      // FIXME: If using Z3 as the core solver the emitted file is actually SMT-LIBv2 not CVC which is a bit confusing
    m_interpreter->getConstraintLog(state, constraints, Interpreter::STP);
    printf("[%s:%d] STP '%s'\n", __FUNCTION__, __LINE__, constraints.c_str());
    m_interpreter->getConstraintLog(state, constraints, Interpreter::SMTLIB2);
    printf("[%s:%d] SMTLIB '%s'\n", __FUNCTION__, __LINE__, constraints.c_str());
    if (m_symPathWriter) {
      std::vector<unsigned char> symbolicBranches;
      m_symPathWriter->readStream(m_interpreter->getSymbolicPathStreamID(state), symbolicBranches);
printf("[%s:%d] SYMPATH\n", __FUNCTION__, __LINE__);
      for (auto I = symbolicBranches.begin(), E = symbolicBranches.end(); I!=E; ++I)
        llvm::outs() << *I << "\n";
    }
printf("[%s:%d] COVERED\n", __FUNCTION__, __LINE__);
      std::map<const std::string*, std::set<unsigned> > cov;
      m_interpreter->getCoveredLines(state, cov);
      for (auto it = cov.begin(), ie = cov.end(); it != ie; ++it)
          for (auto it2 = it->second.begin(), ie = it->second.end(); it2 != ie; ++it2)
              llvm::outs() << *it->first << ":" << *it2 << "\n";
printf("[%s:%d] end\n", __FUNCTION__, __LINE__);
}

int main(int argc, char **argv, char **envp)
{
  std::string ErrorMsg;
  DebugFlag = true;
  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();
  cl::SetVersionPrinter(klee::printVersion); 
  cl::ParseCommandLineOptions(argc, (char **)argv, " klee\n"); // removes // warning
  sys::PrintStackTraceOnErrorSignal();
  auto Buffer = MemoryBuffer::getFileOrSTDIN(InputFile.c_str());
  if (!Buffer)
    klee_error("error loading program '%s': %s", InputFile.c_str(), Buffer.getError().message().c_str());
  auto mainModuleOrError = getLazyBitcodeModule(std::move(Buffer.get()), getGlobalContext());
  if (!mainModuleOrError)
    klee_error("error loading program '%s': %s", InputFile.c_str(), mainModuleOrError.getError().message().c_str());
  Buffer->release();
  Module *mainModule = mainModuleOrError->release();
  if (auto ec = mainModule->materializeAllPermanently())
    klee_error("error loading program '%s': %s", InputFile.c_str(), ec.message().c_str());
  std::string LibraryDir = KleeHandler::getRunTimeLibraryPath(argv[0]);
  for (auto libs_it = LinkLibraries.begin(), libs_ie = LinkLibraries.end(); libs_it != libs_ie; ++libs_it) {
    const char * libFilename = libs_it->c_str();
    klee_message("Linking in library: %s.\n", libFilename);
    mainModule = klee::linkWithLibrary(mainModule, libFilename);
  }
  Function *mainFn = mainModule->getFunction("main");
  if (!mainFn) {
    llvm::outs() << "'main' function not found in module.\n";
    return -1;
  }
  char **pArgv = new char *[InputArgv.size() + 1];
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
  Interpreter::ModuleOptions Opts(LibraryDir.c_str(), OptimizeModule); 
  const Module *finalModule = interpreter->setModule(mainModule, Opts);
printf("[%s:%d] before runFunctionAsMain\n", __FUNCTION__, __LINE__);
  interpreter->runFunctionAsMain(mainFn, InputArgv.size() + 1, pArgv, envp);
  uint64_t queries = stats::queries;
  llvm::outs() << "KLEE: done: explored paths = " << 1 + stats::forks << "\n";

  // Write some extra information in the info file which users won't
  // necessarily care about or understand.
  if (queries)
    llvm::outs() << "KLEE: done: avg. constructs per query = " << stats::queryConstructs / queries << "\n";
  llvm::outs()
    << "KLEE: done: total queries = " << queries << "\n"
    << "KLEE: done: valid queries = " << stats::queriesValid << "\n"
    << "KLEE: done: invalid queries = " << stats::queriesInvalid << "\n"
    << "KLEE: done: query cex = " << stats::queryCounterexamples << "\n"
    << "KLEE: done: total instructions = " << stats::instructions << "\n";
  return 0;
}
