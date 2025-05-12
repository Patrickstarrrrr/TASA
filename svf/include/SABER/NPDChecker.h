#ifndef NPDCHECK_H_
#define NPDCHECK_H_

#include "SABER/LeakChecker.h"

namespace SVF
{

/*!
 * File open/close checker to check consistency of file operations
 */

class NPDChecker : public LeakChecker
{

public:

    /// Constructor
    NPDChecker(): LeakChecker()
    {
    }

    /// Destructor
    virtual ~NPDChecker()
    {
    }

    /// We start from here
    virtual bool runOnModule(SVFIR* pag) override
    {
        /// start analysis
        analyze(pag->getModule());
        return false;
    }

    virtual void initSrcs() override;
    virtual void initSnks() override;
    
    inline bool isSourceLikeFun(const SVFFunction* fun) override
    {
        return false;
    }
    /// Whether the function is a heap deallocator (free/release memory)
    inline bool isSinkLikeFun(const SVFFunction* fun) override
    {
        return false;
    }
    /// Report file/close bugs
    void reportBug(ProgSlice* slice) override ; 
};

} // End namespace SVF

#endif /* FILECHECK_H_ */
