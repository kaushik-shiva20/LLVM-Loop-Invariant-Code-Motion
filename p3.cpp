#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/LoopInfo.h"

#include "llvm/Support/GenericDomTree.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/Loads.h"
#include "llvm/Transforms/Scalar/LICM.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemorySSA.h"
//#include "llvm/PassAnalysisSupport.h"
#include "llvm/Analysis/MemorySSAUpdater.h"


using namespace llvm;
bool canMoveOutOfLoop(Loop *L, Instruction *I, DominatorTree *DT);
static void LoopInvariantCodeMotion(Module &M);

static void summarize(Module *M);
static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        Mem2Reg("mem2reg",
                cl::desc("Perform memory to register promotion before LICM."),
                cl::init(false));

static cl::opt<bool>
        CSE("cse",
                cl::desc("Perform CSE before LICM."),
                cl::init(false));

static cl::opt<bool>
        NoLICM("no-licm",
              cl::desc("Do not perform LICM optimization."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    LLVMContext Context;

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);

    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // If requested, do some early optimizations
    if (Mem2Reg || CSE)
    {
        legacy::PassManager Passes;
	if (Mem2Reg)
	  Passes.add(createPromoteMemoryToRegisterPass());
	if (CSE)
	  Passes.add(createEarlyCSEPass());
        Passes.run(*M.get());
    }

    if (!NoLICM) {
        LoopInvariantCodeMotion(*M.get());
    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());

    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M) {
    for (auto i = M->begin(); i != M->end(); i++) {
        if (i->begin() != i->end()) {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++) {
            for (auto k = j->begin(); k != j->end(); k++) {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I)) {
                    nLoads++;
                } else if (isa<StoreInst>(&I)) {
                    nStores++;
                }
            }
        }
    }
}

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}

static llvm::Statistic NumLoops = {"", "NumLoops", "number of loops analyzed"};
static llvm::Statistic NumLoopsWithCall = {"", "NumLoopsWithCall", "number of loops with a call"};
static llvm::Statistic NumLoopsNoLoads = {"", "NumLoopsNoLoads", "number of loops analyzed without loads"};
static llvm::Statistic NumLoopsNoStores = {"", "NumLoopsNoStores", "number of loops analyzed without stores"};
// add other stats
static llvm::Statistic LICMBasic = {"", "LICMBasic", "basic loop invariant instructions"};
static llvm::Statistic LICMLoadHoist = {"", "LICMLoadHoist", "loop invariant load instructions"};
static llvm::Statistic LICMNoPreheader = {"", "LICMNoPreheader", "absence of preheader prevents optimization"};


bool instrIsInLoop(Loop *loop, Instruction *instr) {
    if (loop->contains(instr))
    {
        return true;
    }else
    {
        for (auto subLoop : loop->getSubLoops()) {
            if (instrIsInLoop(subLoop, instr)) return true;
        }

        return false;
    }

}

bool hasAStore = false;
/*This function updates NumLoopsNoLoads stat*/
static void numStats(Module &M) {
    bool containsLoad = false;

    /*loop over all the functions in this module M*/
    for (auto f = M.begin(); f != M.end(); f++) {
        if (f->empty()) continue;

        LoopInfoBase<BasicBlock, Loop> *LI = new LoopInfoBase<BasicBlock, Loop>();
        DominatorTreeBase<BasicBlock, false> *DT = new DominatorTreeBase<BasicBlock, false>();
        DominatorTree mDT(*f);

        DT->recalculate(*f); // dominance for Function, F
        LI->analyze(*DT); // calculate loop info
        /*loop over all the Loops present in this function f*/
        for (auto li: *LI) {
            if(li == nullptr) continue;
            containsLoad = false;
            /*loop over all the blocks present in this Loop li*/
            for(auto bb:li->blocks()) {
                if (bb->empty()) continue;
                /*loop over all the instructions present in this block bb*/
                for (auto i = bb->begin(); i != bb->end();i++) {
                    if(i->getOpcode() == Instruction::Load) {
                        containsLoad = true;
                        break;
                    }
                }
                if(containsLoad) break;
            }
            if (!containsLoad) {
                NumLoopsNoLoads++;
            }
        }
    }
}

/*This function performs LICM on the given loop li*/
bool mLICM(Loop *li, DominatorTree *mDT)
{
    bool mRetVal=false;
    bool isOpt = false;
    hasAStore = false;
    static Loop *prevLoop = nullptr;

    /*loop over all blocks in Loop li*/
    for(auto bb:li->blocks())
    {
        if(bb->empty()) continue;
        /*loop over all instructions in Block bb*/
        for (auto i = bb->begin(); i != bb->end();)
        {
            Instruction *Inst = &*i++;
            //check if instruction is load or store
            if (Inst->getOpcode() == Instruction::Load) {
                if(canMoveOutOfLoop(li, Inst, mDT))
                {
                    isOpt = true;
                    /*Move the loop invariant instruction to preheader*/
                    Instruction *mClone = Inst->clone();
                    //mClone->setName(Inst->getName());
                    mClone->insertBefore(li->getLoopPreheader()->getTerminator());
                    Inst->replaceAllUsesWith(mClone);
                    i=Inst->eraseFromParent();
                    LICMLoadHoist++;
                    for (auto ui = Inst->user_begin(); ui != Inst->user_end();) {
                        Instruction *user = cast<Instruction>(*ui++);
                        if (li->contains(user->getParent())) {
                            mRetVal=true;
                            break;
                        }
                    }
                    /*re run LICM for this loop as an invariant instruction is detected*/
                }
            } else if (Inst->getOpcode() == Instruction::Store) {
            } else {
                bool changed = false;
                /*check if an instruction is loop invariant and hoist it if possible*/
                if (li->makeLoopInvariant(Inst, changed, nullptr, nullptr)) {
                    if(changed) {
                        LICMBasic++;
                        //find uses of the instruction in the loop
                        for (auto ui = Inst->user_begin(); ui != Inst->user_end();) {
                            Instruction *user = cast<Instruction>(*ui++);
                            if (li->contains(user->getParent())) {
                                mRetVal=true;
                                break;
                            }
                        }
                    }
                }
            }
        }
    }
    if(prevLoop == nullptr || prevLoop != li) {
        prevLoop = li;
        if (isOpt) {
            if (!hasAStore) {
                NumLoopsNoStores++;
            }
        }
    }
    return mRetVal;
}

static void LoopInvariantCodeMotion(Module &M)
{
    /*loop over all the functions in this Module M*/
    for(auto f = M.begin(); f!=M.end(); f++)
    {
        if (f->empty()) continue;

        LoopInfoBase<BasicBlock, Loop> *LI = new LoopInfoBase<BasicBlock, Loop>();
        DominatorTreeBase<BasicBlock, false> *DT = new DominatorTreeBase<BasicBlock, false>();
        DominatorTree mDT(*f);

        DT->recalculate(*f); // dominance for Function, F
        LI->analyze(*DT); // calculate loop info

        /*loop over all the Loops present in this function f*/
        for (auto li: *LI)
        {
            //li is a Loop*, consider each one
            if(li == nullptr) continue;
            BasicBlock *Preheader = li->getLoopPreheader();
            /*Skip this loop if it doesn't have a preheader*/
            if (Preheader == nullptr)
            {
                LICMNoPreheader++;
                continue;
            }
            //subloops
            int mCntr=0;
            for(auto subli: li->getSubLoops())
            {
                NumLoops++;
                while(mLICM(subli, &mDT)) {
                    mCntr++;
                }
            }
            NumLoops++;

            while(mLICM(li, &mDT)) {
                mCntr++;
            }
        }
    }
    numStats(M);
}

/*This function returns true if its safe to hoist the load instruction*/
bool canMoveOutOfLoop(Loop *L, Instruction *I, DominatorTree *DT) {

    static Loop *prev=nullptr;

    /*Check if Instruction is volatile*/
    if (I->isVolatile()) return false;

    /*Check if loop contains a call instruction*/
    for (auto bb: L->blocks()) {
        if(bb->empty()) continue;
        for (auto i = bb->begin(); i != bb->end();i++) {
            Instruction *Inst = &*i;
            if (Inst->getOpcode() == Instruction::Call) {
                if(prev == nullptr || prev != L) {
                    prev = L;
                    NumLoopsWithCall++;
                }
                return false;
            }
        }
    }

    Value *addr = I->getOperand(0);

    /*addr is a GlobalVariable and there are no possible stores to addr in L*/
    if ((isa<Constant>(addr)) || (isa<AllocaInst>(addr)))
    {

        //check if the loop has any conflicting store
        for (auto bb: L->blocks()) {
            if(bb->empty()) continue;
            for (auto i = bb->begin(); i != bb->end();i++) {
                Instruction *Inst = &*i;
                if (Inst->getOpcode() == Instruction::Store) {
                    if((!(isa<Constant>(Inst->getOperand(1)))) && (!(isa<AllocaInst>(Inst->getOperand(1))))) {
                        hasAStore = true;
                       // return false;
                    }
                    if (Inst->getOperand(1) == addr) {
                        hasAStore = true;
                        return false;
                    }
                }
            }
        }

        if (isa<AllocaInst>(addr))
        {
            //additional check for alloca
            //check if addr instruction is in loop
            if(instrIsInLoop(L, cast<Instruction>(addr))) return false;
        }

        return true;
    }
    /*there are no possible stores to any addr in L && addr is loop invariant && I dominates L’s exit*/
    else {
        //check if the loop has a store
        for (auto bb: L->blocks()) {
            if(bb->empty()) continue;
            for (auto i = bb->begin(); i != bb->end();i++) {
                Instruction *Inst = &*i;
                if (Inst->getOpcode() == Instruction::Store) {
                    hasAStore = true;
                    return false;
                }
            }
        }

        //check in instruction is in loop
        if(instrIsInLoop(L, cast<Instruction>(addr))) return false;

        //check if the block containing instruction dominates all loop exits
        for (auto bb: L->blocks()) {
            if (L->isLoopExiting(bb)) {
                if (!DT->dominates(I->getParent(), bb)) {
                    return false;
                }
            }
        }
        return true;
    }
}
