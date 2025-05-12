#include "SABER/UAFChecker.h"
#include "Util/SVFUtil.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;

void UAFChecker::reportBug(ProgSlice* slice)
{
    if(slice->isSatisfiableForSinkToUser() == false)
    {
        GenericBug::EventStack eventStack;
        slice->evalFinalCond2Event(eventStack);
        eventStack.push_back(
            SVFBugEvent(SVFBugEvent::SourceInst, getSrcCSID(slice->getSource())));
        report.addSaberBug(GenericBug::USEAFTERFREE, eventStack);
    }
    // if(Options::ValidateTests())
    //     testsValidation(slice);
}