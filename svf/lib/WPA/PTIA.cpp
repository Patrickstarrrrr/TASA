#include "WPA/PTIA.h"

using namespace SVF;
using namespace SVFUtil;
using namespace std;

PTIA::PTIA(ConstraintGraph* g)
{
    consCG = g;
    buildPTIG();
}

// void PTIA::buildPTIG()
// {
//     ptg = new ConstraintGraph(consCG->getSVFIR());
//     ptg->initialize();
//     ptg->solveWorklist();
//     ptg->finalize();
// }