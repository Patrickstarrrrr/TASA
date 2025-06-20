//===- Options.h -- Command line options ------------------------//

#ifndef OPTIONS_H_
#define OPTIONS_H_

#include <sstream>
#include "FastCluster/fastcluster.h"
#include "Util/CommandLine.h"
#include "Util/PTAStat.h"
#include "MemoryModel/PointerAnalysisImpl.h"
#include "Util/NodeIDAllocator.h"
#include "MSSA/MemSSA.h"
#include "WPA/WPAPass.h"

namespace SVF
{

/// Carries around command line options.
class Options
{
public:
    Options(void) = delete;

    static const OptionMap<enum PTAStat::ClockType> ClockType;

    /// If set, only return the clock when getClk is called as getClk(true).
    /// Retrieving the clock is slow but it should be fine for a few calls.
    /// This is good for benchmarking when we don't need to know how long processLoad
    /// takes, for example (many calls), but want to know things like total solve time.
    /// Should be used only to affect getClk, not CLOCK_IN_MS.
    static const Option<bool> MarkedClocksOnly;

    /// Allocation strategy to be used by the node ID allocator.
    /// Currently dense, seq, or debug.
    static const OptionMap<SVF::NodeIDAllocator::Strategy> NodeAllocStrat;

    /// Maximum number of field derivations for an object.
    static const Option<u32_t> MaxFieldLimit;

    /// Whether to stage Andersen's with Steensgaard and cluster based on that data.
    static const Option<bool> ClusterAnder;

    /// Whether to cluster FS or VFS with the auxiliary Andersen's.
    static const Option<bool> ClusterFs;

    /// Use an explicitly plain mapping with flow-sensitive (not null).
    static const Option<bool> PlainMappingFs;

    /// Type of points-to set to use for all analyses.
    static const OptionMap<PointsTo::Type> PtType;

    /// Clustering method for ClusterFs/ClusterAnder.
    /// TODO: we can separate it into two options, and make Clusterer::cluster take in a method
    ///       argument rather than plugging Options::ClusterMethod *inside* Clusterer::cluster
    ///       directly, but it seems we will always want single anyway, and this is for testing.
    static const OptionMap<enum hclust_fast_methods> ClusterMethod;

    /// Cluster partitions separately.
    static const Option<bool> RegionedClustering;

    /// Align identifiers in each region to a word.
    static const Option<bool> RegionAlign;

    /// Predict occurrences of points-to sets in the staged points-to set to
    /// weigh more common points-to sets as more important.
    static const Option<bool> PredictPtOcc;

    /// PTData type.
    static const OptionMap<BVDataPTAImpl::PTBackingType> ptDataBacking;

    /// Time limit for the main phase (i.e., the actual solving) of FS analyses.
    static const Option<u32_t> FsTimeLimit;

    /// Time limit for the Andersen's analyses.
    static const Option<u32_t> AnderTimeLimit;

    /// Number of threads for the versioning phase.
    static const Option<u32_t> VersioningThreads;

    // ContextDDA.cpp
    static const Option<u32_t> CxtBudget;

    // DDAPass.cpp
    static const Option<u32_t> MaxPathLen;
    static const Option<u32_t> MaxContextLen;
    static const Option<u32_t> MaxStepInWrapper;
    static const Option<std::string> UserInputQuery;
    static const Option<bool> InsenRecur;
    static const Option<bool> InsenCycle;
    static const Option<bool> PrintCPts;
    static const Option<bool> PrintQueryPts;
    static const Option<bool> WPANum;
    static OptionMultiple<PointerAnalysis::PTATY> DDASelected;

    // FlowDDA.cpp
    static const Option<u32_t> FlowBudget;

    // Offline constraint graph (OfflineConsG.cpp)
    static const Option<bool> OCGDotGraph;

    // Program Assignment Graph for pointer analysis (SVFIR.cpp)
    static Option<bool> HandBlackHole;
    static const Option<bool> FirstFieldEqBase;

    // SVFG optimizer (SVFGOPT.cpp)
    static const Option<bool> ContextInsensitive;
    static const Option<bool> KeepAOFI;
    static const Option<std::string> SelfCycle;

    // Sparse value-flow graph (VFG.cpp)
    static const Option<bool> DumpVFG;

    // Base class of pointer analyses (PointerAnalysis.cpp)
    static const Option<bool> TypePrint;
    static const Option<bool> FuncPointerPrint;
    static const Option<bool> PTSPrint;
    static const Option<bool> PTSAllPrint;
    static const Option<bool> PrintFieldWithBasePrefix;
    static const Option<bool> PStat;
    static const Option<u32_t> StatBudget;
    static const Option<bool> PAGDotGraph;
    static const Option<bool> ShowSVFIRValue;
    static const Option<bool> DumpICFG;
    static const Option<std::string> DumpJson;
    static const Option<bool> ReadJson;
    static const Option<bool> CallGraphDotGraph;
    static const Option<bool> PAGPrint;
    static const Option<u32_t> IndirectCallLimit;
    static const Option<bool> UsePreCompFieldSensitive;
    static const Option<bool> EnableAliasCheck;
    static const Option<bool> EnableTypeCheck;
    static const Option<bool> EnableThreadCallGraph;
    static const Option<bool> ConnectVCallOnCHA;

    // PointerAnalysisImpl.cpp
    static const Option<bool> INCDFPTData;

    // Memory region (MemRegion.cpp)
    static const Option<bool> IgnoreDeadFun;

    // Base class of pointer analyses (MemSSA.cpp)
    static const Option<bool> DumpMSSA;
    static const Option<std::string> MSSAFun;
    // static const llvm::cl::opt<string> MSSAFun;
    static const OptionMap<MemSSA::MemPartition> MemPar;

    // SVFG builder (SVFGBuilder.cpp)
    static const Option<bool> SVFGWithIndirectCall;
    static Option<bool> OPTSVFG;

    static const Option<std::string> WriteSVFG;
    static const Option<std::string> ReadSVFG;

    // LockAnalysis.cpp
    static const Option<bool> IntraLock;
    static const Option<bool> PrintLockSpan;

    // MHP.cpp
    static const Option<bool> PrintInterLev;
    static const Option<bool> DoLockAnalysis;

    //MTAStat.cpp
    static const Option<bool> AllPairMHP;

    // TCT.cpp
    static const Option<bool> TCTDotGraph;

    // LeakChecker.cpp
    static const Option<bool> ValidateTests;

    // Source-sink analyzer (SrcSnkDDA.cpp)
    static const Option<bool> DumpSlice;
    static const Option<u32_t> CxtLimit;

    // CHG.cpp
    static const Option<bool> DumpCHA;

    // DCHG.cpp
    static const Option<bool> PrintDCHG;

    // LLVMModule.cpp
    static const Option<std::string> Graphtxt;
    static const Option<bool> SVFMain;

    // SymbolTableInfo.cpp
    static const Option<bool> LocMemModel;
    static const Option<bool> ModelConsts;
    static const Option<bool> ModelArrays;
    static const Option<bool> CyclicFldIdx;
    static const Option<bool> SymTabPrint;

    // Conditions.cpp
    static const Option<u32_t> MaxZ3Size;

    // BoundedZ3Expr.cpp
    static const Option<u32_t> MaxBVLen;

    // SaberCondAllocator.cpp
    static const Option<bool> PrintPathCond;

    // SaberSVFGBuilder.cpp
    static const Option<bool> CollectExtRetGlobals;

    // SVFUtil.cpp
    static const Option<bool> DisableWarn;

    // Andersen.cpp
    static const Option<bool> ConsCGDotGraph;
    static const Option<bool> BriefConsCGDotGraph;
    static const Option<bool> PrintCGGraph;
    // static const Option<string> WriteAnder;
    static const Option<std::string> WriteAnder;
    // static const Option<string> ReadAnder;
    static const Option<std::string> ReadAnder;
    static const Option<bool> DiffPts;
    static Option<bool> DetectPWC;
    static const Option<bool> VtableInSVFIR;

    // WPAPass.cpp
    static const Option<std::string> ExtAPIPath;
    static const Option<bool> AnderSVFG;
    static const Option<bool> SABERFULLSVFG;
    static const Option<bool> PrintAliases;
    static OptionMultiple<PointerAnalysis::PTATY> PASelected;
    static OptionMultiple<WPAPass::AliasCheckRule> AliasRule;

    // DOTGraphTraits
    static const Option<bool> ShowHiddenNode;

    // CFL option
    static const Option<std::string> GrammarFilename;
    static const Option<std::string> CFLGraph;
    static const Option<bool> PrintCFL;
    static const Option<bool> FlexSymMap;
    static const Option<bool>  PEGTransfer;
    static const Option<bool>  CFLSVFG;
    static const Option<bool> POCRAlias;
    static const Option<bool> POCRHybrid;
    static const Option<bool> Customized;

    // Loop Analysis
    static const Option<bool> LoopAnalysis;
    static const Option<u32_t> LoopBound;

    // Abstract Execution
    static const Option<u32_t> WidenDelay;
    /// the max time consumptions (seconds). Default: 4 hours 14400s
    static const Option<u32_t> Timeout;
    /// bug info output file, Default: output.db
    static const Option<std::string> OutputName;
    /// buffer overflow checker, Default: false
    static const Option<bool> BufferOverflowCheck;
    /// memory leak check, Default: false
    static const Option<bool> MemoryLeakCheck;
    /// file open close checker, Default: false
    static const Option<bool> FileCheck;
    /// double free checker, Default: false
    static const Option<bool> DFreeCheck;
    /// uaf checker, Default: false
    static const Option<bool> UAFCheck;
    /// npd checker, Default: false
    static const Option<bool> NPDCheck;
    /// data race checker, Default: false
    static const Option<bool> RaceCheck;
    /// if the access index of gepstmt is unknown, skip it, Default: false
    static const Option<bool> GepUnknownIdx;
    static const Option<bool> RunUncallFuncs;

    static const Option<bool> ICFGMergeAdjacentNodes;

    // float precision for symbolic abstraction
    static const Option<u32_t> AEPrecision;


    static const Option<bool> ComputeInputReachable;
    static const Option<bool> PrintInputReachable;
    static const Option<bool> PrintDFBugSinkInfo;
    static const Option<bool> BranchBBInfo;
    static const Option<bool> EnablePTIG;
    
    static const Option<bool> SVFGVariableName;
};
}  // namespace SVF

#endif  // ifdef OPTIONS_H_
