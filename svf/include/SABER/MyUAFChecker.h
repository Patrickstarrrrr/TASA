#ifndef MYUAFCHECKER_H_
#define MYUAFCHECKER_H_

#include "SABER/LeakChecker.h"
#include "Util/GeneralType.h"

namespace SVF
{

/*!
 * UAF checker to check deallocations of memory
 */

class MyUAFChecker : public LeakChecker
{

public:
    /// Constructor
    MyUAFChecker(): LeakChecker()
    {
    }

    /// Destructor
    virtual ~MyUAFChecker()
    {
    }

    /// We start from here
    virtual bool runOnModule(SVFIR* pag) override
    {
        /// start analysis
        analyze(pag->getModule());
        return false;
    }

    // virtual void initSrcs() override;
    virtual void initSnks() override;

    /// Report file/close bugs
    void reportBug(ProgSlice* slice) override;

    NodeBS freeSinkSVFGNodes;
    NodeBS useSinkSVFGNodes;
    

    // NodeBS useSVFGNodes;
};

} // End namespace SVF

#endif /* MYUAFCHECKER_H_ */