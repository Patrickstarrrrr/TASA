#ifndef PTIA_H_
#define PTIA_H_

#include "Andersen.h"
#include "Graphs/ConsG.h"

namespace SVF
{
class PTIA
{
public:
    ConstraintGraph* ptg;
    ConstraintGraph* consCG;
    PTIA(ConstraintGraph* g);
private:
    void buildPTIG();
};

} // end namespace SVF

#endif