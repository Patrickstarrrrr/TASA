#ifndef UAFCHECKER_H_
#define UAFCHECKER_H_

#include "SABER/LeakChecker.h"
#include "Util/GeneralType.h"

namespace SVF
{

/*!
 * UAF checker to check deallocations of memory
 */

class UAFChecker : public LeakChecker
{

public:
    /// Constructor
    UAFChecker(): LeakChecker()
    {
    }

    /// Destructor
    virtual ~UAFChecker()
    {
    }

    /// We start from here
    virtual bool runOnModule(SVFIR* pag) override
    {
        /// start analysis
        analyze(pag->getModule());
        return false;
    }

    /// Report file/close bugs
    void reportBug(ProgSlice* slice) override;


    /// Validate test cases for regression test purpose
    // void testsValidation(ProgSlice* slice);
    // void validateSuccessTests(ProgSlice* slice, const SVFFunction* fun);
    // void validateExpectedFailureTests(ProgSlice* slice, const SVFFunction* fun);
};

} // End namespace SVF

#endif /* UAFCHECKER_H_ */