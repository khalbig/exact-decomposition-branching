/**@file   main.cpp
 * @brief  Exact Decomposition Branching using Delta-regularity
 * @author Katrin Halbig
 */

#include <iostream>
#include <fstream>
#include <chrono>
#include <vector>
#include "objscip/objscip.h"
#include "objscip/objscipdefplugins.h"

using namespace std;
using namespace std::chrono;

//#define PRINT_SUBMIP_INFO

/** structures */

enum NodeStatus
{
    NODE_STATUS_OPEN,
    NODE_STATUS_BRANCHED,
    NODE_STATUS_INFEASIBLE,
    NODE_STATUS_PRUNEBOUND,
    NODE_STATUS_UNBOUNDED,
    NODE_STATUS_OPTIMAL,
    NODE_STATUS_INVALID
};

struct Node
{
    SCIP *scip;
    Node *parent;                /* pointer to parent node */
    vector<Node *> children;     /* pointers to children */
    int idx;                     /* consecutive unique number */
    int depth;                   /* root node has depth 0 */
    NodeStatus status;           /* status of node */
    vector<SCIP_Rational**> rhs; /* for each linking: values of right-hand side in this node */
    vector<SCIP_Rational**> lhs; /* for each linking: values of left-hand side in this node */
    int nlinking;                /* number of linking constraints */
    int nblocks;                 /* number of blocks */

    /* reserves memory and initializes with default value */
    Node(SCIP* scip, int nblocks, int nlinking)
    {
        rhs.resize(nlinking + 1); /* last entry corresponds to objective function */
        lhs.resize(nlinking + 1); /* last entry corresponds to objective function */
        for (int i = 0; i < nlinking + 1; i++)
        {
            RatCreateBlockArray(SCIPblkmem(scip), &rhs[i], nblocks);
            RatCreateBlockArray(SCIPblkmem(scip), &lhs[i], nblocks);
        }
        children.resize(nlinking + 1); /* maximal number of child nodes (last for objective function) */
        this->nlinking = nlinking;
        this->nblocks = nblocks;
        this->scip = scip;
    }
    ~Node(){
        for (int i = this->nlinking; i >= 0; i--)
        {
            RatFreeBlockArray(SCIPblkmem(scip), &lhs[i], this->nblocks);
            RatFreeBlockArray(SCIPblkmem(scip), &rhs[i], this->nblocks);
        }
        lhs.clear();
        rhs.clear();
    }
};

/** classes */

/* contains all information of considered problem */
class Problem
{
public:
    void setdelta(int delta);
    void settimelimit(int time);
    void setepsilon(int nom, int denom);
    SCIP_RETCODE create(const char **instancefile, const char **decfile, const char **metafile);
    SCIP_RETCODE readfiles(const char **instancefile, const char **decfile, const char **metafile);
    SCIP_RETCODE createsubMIPs();
    SCIP_RETCODE addroot();
    SCIP_RETCODE run(time_point<std::chrono::system_clock> t_run_start);
    Node *selectNode();
    void updateLP(Node *node);
    SCIP_RETCODE updatesubMIP(SCIP *subMIP, Node *node, SCIP_SOL *sublpsol, int block);
    SCIP_RETCODE handlenode(Node *node, NodeStatus *status);
    SCIP_RETCODE branch(Node *node, SCIP *submip, SCIP_Rational *blocksolval, SCIP_SOL *sublpsol, int block);
    SCIP_RETCODE checksol();
    SCIP_RETCODE freenodes();
    SCIP_RETCODE free();
    SCIP *scipcopy; /* to check solution */
    SCIP_SOL *DBsol = NULL;
    Problem(){
        RatCreate(&this->epsilon);
        RatCreate(&this->delta);
        RatCreate(&this->incumbent);
    }
    ~Problem(){
        RatFree(&this->incumbent);
        RatFree(&this->delta);
        RatFree(&this->epsilon);
    }
private:
    SCIP *origscip; /* is later changed to LP relaxation */
    SCIP_DECOMP *decomp;
    vector<SCIP *> subMIPs; /* subproblem for each block */
    vector<Node *> nodes;
    vector<SCIP_SOL *> solutionstorage;
    vector<int> linkingsign;                       /* 0: equation, 1: lessequal, 2: greaterequal */
    vector<vector<SCIP_CONS *>> linkingpartsorig;  /* for each linking constraint: part of block in origscip (last one is obj) */
    vector<vector<SCIP_CONS *>> linkingpartsblock; /* for each block: part of linking constraint in subMIP (last one is obj) */
    vector<SCIP_HASHMAP *> varsmaps;               /* for each block, hashmap mapping origvar -> subMIPvar */
    SCIP_Rational *incumbent;
    int nblocks;
    int nlinking;
    int nnodes = 0;
    long maxnodes = 1e15;   /* maximal number of nodes */
    int maxtime = 3600;     /* timelimit in seconds */
    SCIP_Rational *epsilon; /* should be greater than feastol */
    SCIP_Rational *delta;   /* positive integer; zero if not used for rounding */
};

/** functions */

/* round down to 1/delta*Z (strict less) */
SCIP_RETCODE deltafloorstrict(SCIP *scip, SCIP_Rational *x, SCIP_Rational * delta, SCIP_Rational *result)
{
    assert(RatIsIntegral(delta));
    assert(RatIsPositive(delta));
    long long floorint;
    SCIP_Rational* tmp;
    SCIP_Rational* tmp2;

    if( RatIsInfinity(x) || RatIsNegInfinity(x) )
    {
        RatSet(result, x);
        return SCIP_OKAY;
    }

    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp) );
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp2) );
    RatMult(tmp, x, delta);
    RatRoundInteger(&floorint, tmp, SCIP_R_ROUND_DOWNWARDS);
    RatSetInt(tmp, floorint, 1);
    RatDiv(tmp2, tmp, delta);

    /* strict less */
    if (RatIsEqual(x, tmp2))
    {
        RatInvert(tmp, delta); /* 1/delta */
        RatDiff(result, tmp2, tmp);
    }
    else
    {
        RatSet(result, tmp2);
    }

    RatFreeBuffer(SCIPbuffer(scip), &tmp2);
    RatFreeBuffer(SCIPbuffer(scip), &tmp);

    return SCIP_OKAY;
}

/* round down to 1/delta*Z */
SCIP_RETCODE deltafloor(SCIP *scip, SCIP_Rational *x, SCIP_Rational * delta, SCIP_Rational *result)
{
    assert(RatIsIntegral(delta));
    assert(RatIsPositive(delta));
    long long floorint;
    SCIP_Rational* tmp;
    SCIP_Rational* tmp2;

    if( RatIsInfinity(x) || RatIsNegInfinity(x) )
    {
        RatSet(result, x);
        return SCIP_OKAY;
    }

    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp) );
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp2) );
    RatMult(tmp, x, delta);
    RatRoundInteger(&floorint, tmp, SCIP_R_ROUND_DOWNWARDS);
    RatSetInt(tmp, floorint, 1);
    RatDiv(tmp2, tmp, delta);

    RatSet(result, tmp2);

    RatFreeBuffer(SCIPbuffer(scip), &tmp2);
    RatFreeBuffer(SCIPbuffer(scip), &tmp);

    return SCIP_OKAY;
}

/* round up to 1/delta*Z (strict greater) */
SCIP_RETCODE deltaceilstrict(SCIP *scip, SCIP_Rational *x, SCIP_Rational * delta, SCIP_Rational *result)
{
    assert(RatIsIntegral(delta));
    assert(RatIsPositive(delta));
    long long ceilint;
    SCIP_Rational* tmp;
    SCIP_Rational* tmp2;

    if( RatIsInfinity(x) || RatIsNegInfinity(x) )
    {
        RatSet(result, x);
        return SCIP_OKAY;
    }

    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp) );
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp2) );
    RatMult(tmp, x, delta);
    RatRoundInteger(&ceilint, tmp, SCIP_R_ROUND_UPWARDS);
    RatSetInt(tmp, ceilint, 1);
    RatDiv(tmp2, tmp, delta);

    /* strict greater */
    if (RatIsEqual(x, tmp2))
    {
        RatInvert(tmp, delta); /* 1/delta */
        RatAdd(result, tmp2, tmp);
    }
    else
    {
        RatSet(result, tmp2);
    }

    RatFreeBuffer(SCIPbuffer(scip), &tmp2);
    RatFreeBuffer(SCIPbuffer(scip), &tmp);

    return SCIP_OKAY;
}

/* round up to 1/delta*Z */
SCIP_RETCODE deltaceil(SCIP *scip, SCIP_Rational *x, SCIP_Rational * delta, SCIP_Rational *result)
{
    assert(RatIsIntegral(delta));
    assert(RatIsPositive(delta));
    long long ceilint;
    SCIP_Rational* tmp;
    SCIP_Rational* tmp2;

    if( RatIsInfinity(x) || RatIsNegInfinity(x) )
    {
        RatSet(result, x);
        return SCIP_OKAY;
    }

    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp) );
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(scip), &tmp2) );
    RatMult(tmp, x, delta);
    RatRoundInteger(&ceilint, tmp, SCIP_R_ROUND_UPWARDS);
    RatSetInt(tmp, ceilint, 1);
    RatDiv(tmp2, tmp, delta);

    RatSet(result, tmp2);

    RatFreeBuffer(SCIPbuffer(scip), &tmp2);
    RatFreeBuffer(SCIPbuffer(scip), &tmp);

    return SCIP_OKAY;
}

/* creates new problem
 *
 * reads from files or generates instance with decomposition
 * initializes origscip, nblocks, nlinking, decomp
 */
SCIP_RETCODE Problem::create(
    const char **instancefile, /* path to instance file, or NULL */
    const char **decfile,      /* path to decomposition file, or NULL */
    const char **metafile      /* path to meta file, or NULL */
)
{
    int ndecomps;
    SCIP_DECOMP **decomps;

    /* initialize SCIP */
    this->origscip = NULL;
    SCIP_CALL(SCIPcreate(&this->origscip));

    /* include default SCIP plugins */
    SCIP_CALL(SCIPincludeDefaultPlugins(this->origscip));
    SCIP_CALL(SCIPsetBoolParam(this->origscip, "exact/enabled", TRUE));

    readfiles(instancefile, decfile, metafile);

    SCIP_CALL(SCIPsetIntParam(this->origscip, "display/verblevel", 0));
    SCIP_CALL( SCIPsetPresolving(this->origscip, SCIP_PARAMSETTING_OFF, TRUE) ); /* disable presolving since it is only implemented exact if using papilo */

    /* store decomposition info */
    SCIPgetDecomps(this->origscip, &decomps, &ndecomps, TRUE);
    assert(ndecomps == 1);
    this->decomp = decomps[0];
    this->nblocks = SCIPdecompGetNBlocks(decomp);
    this->nlinking = SCIPdecompGetNBorderConss(decomp);
    assert(SCIPdecompGetNBorderVars(decomp) == 0);

    /* set variables */
    RatSetString(this->incumbent, "inf");

    /* solve original problem with SCIP to check solution value */
    SCIP_CALL(SCIPcreate(&this->scipcopy));
    SCIPcopy(this->origscip, this->scipcopy, NULL, NULL, "_copy", true, true, false, true, NULL);

    return SCIP_OKAY;
}

/* reads instance and decomposition from file
 * initializes origscip, delta
 */
SCIP_RETCODE Problem::readfiles(const char **instancefile, const char **decfile, const char **metafile)
{
    assert(this->origscip != NULL);
    assert(*instancefile != NULL);
    assert(*decfile!= NULL);

    /* read instance and decomposition */
    printf("Read problem.\n");
    SCIP_CALL(SCIPreadProb(this->origscip, *instancefile, NULL));
    SCIP_CALL(SCIPreadProb(this->origscip, *decfile, "dec"));

    /* read delta from meta file */
    if (*metafile != NULL)
    {
        ifstream metastream(*metafile);
        vector<int> data;
        string line;

        if (!metastream)
        {
            cerr << "Cannot open the File : " << metafile << std::endl;
            return SCIP_NOFILE;
        }

        while (getline(metastream, line))
        {
            if (line.find("delta ", 0) == 0)
            {
                int tmp = stoi(line.substr(line.find_first_of("0123456789"), line.find_last_of("0123456789") + 1 - line.find_first_of("0123456789")));
                setdelta(tmp);
                printf("delta: %d\n", tmp);
            }
        }
        metastream.close();
    }
    else
    {
        setdelta(0);
        RatPrintf("delta: %q\n", this->delta);
    }
    return SCIP_OKAY;
}

/* sets delta */
void Problem::setdelta(int d)
{
    RatSetInt(this->delta, d, 1);
}

/* sets timelimit */
void Problem::settimelimit(int time)
{
    this->maxtime = time;
}

/* sets epsilon */
void Problem::setepsilon(int nom, int denom)
{
    RatSetInt(this->epsilon, nom, denom);
    RatPrintf("epsilon: %q\n", this->epsilon);
}

/* creates subMIPs and relaxes origscip */
SCIP_RETCODE Problem::createsubMIPs()
{
    char name[SCIP_MAXSTRLEN];
    SCIP_VAR **vars;
    SCIP_VAR *newvar;
    SCIP_CONS **conss = NULL;
    SCIP_CONS *newcons;
    SCIP_CONS *newconss[this->nblocks];
    SCIP_CONS *newconssorig[this->nblocks];
    SCIP_VAR **consvars;
    SCIP_Rational **consvals;
    int *conslabels;
    int *varlabels;
    int nconss;
    int nvars;
    SCIP_Bool success;

    SCIP_Rational *neginf;
    SCIP_Rational *posinf;
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &neginf) );
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &posinf) );
    RatSetString(neginf, "-inf");
    RatSetString(posinf, "inf");

    this->subMIPs.resize(this->nblocks); /* reserve enough memory since we know number of blocks with empty elements */
    this->varsmaps.resize(this->nblocks); /* enough memory with empty elements */

    /* create scip for blocks */
    for (int i = 0; i < this->nblocks; i++)
    {
        sprintf(name, "%s_block_%d", SCIPgetProbName(this->origscip), i);
        SCIP_CALL(SCIPcreate(&this->subMIPs[i]));
        SCIP_CALL(SCIPincludeDefaultPlugins(this->subMIPs[i]));
        SCIP_CALL(SCIPsetBoolParam(this->subMIPs[i], "exact/enabled", TRUE));
        SCIP_CALL(SCIPsetIntParam(this->subMIPs[i], "display/verblevel", 0));
        SCIP_CALL( SCIPsetPresolving(this->subMIPs[i], SCIP_PARAMSETTING_OFF, TRUE) ); /* disable presolving since it is only implemented exact if using papilo */
        SCIP_CALL(SCIPcreateProbBasic(this->subMIPs[i], name));
        assert(SCIPisExactSolve(this->subMIPs[i]));
    }

    nconss = SCIPgetNConss(this->origscip);
    nvars = SCIPgetNVars(this->origscip);
    for (int b = 0; b < this->nblocks; b++)
    {
        SCIP_CALL(SCIPhashmapCreate(&this->varsmaps[b], SCIPblkmem(this->origscip), nvars));
    }
    SCIP_CALL(SCIPallocBufferArray(this->origscip, &consvars, nvars));

    /* if problem has no constraints or no variables, return */
    if (nconss == 0 || nvars == 0)
    {
        printf("problem has no constraints or no variables\n");
        return SCIP_ERROR;
    }

    vars = SCIPgetVars(this->origscip);
    SCIP_CALL(SCIPduplicateBufferArray(this->origscip, &conss, SCIPgetConss(this->origscip), nconss)); /* duplicate array since conss are added */
    SCIP_CALL(SCIPallocBufferArray(this->origscip, &conslabels, nconss));
    SCIP_CALL(SCIPallocBufferArray(this->origscip, &varlabels, nconss));
    SCIPdecompGetConsLabels(this->decomp, conss, conslabels, nconss);
    SCIPdecompGetVarsLabels(this->decomp, vars, varlabels, nvars);

    /* add variables of blocks to subMIPs */
    for (int i = 0; i < nvars; i++)
    {
        int block = varlabels[i];
        assert(block < this->nblocks); /* we assume consecutive labels beginning with zero */
        assert(block >= 0); /* no linking variables are allowed */

        SCIP_CALL( SCIPgetVarCopy(this->origscip, this->subMIPs[block], vars[i], &newvar, this->varsmaps[block], NULL, TRUE, &success) );
        assert(success);
        /* copy exact data, if solving exactly */
        if( SCIPisExactSolve(this->subMIPs[block]) && SCIPisExactSolve(this->origscip) )
        {
            SCIP_CALL( SCIPaddVarExactData(this->subMIPs[block], newvar,
                        SCIPvarGetLbGlobalExact(vars[i]), SCIPvarGetUbGlobalExact(vars[i]), SCIPvarGetObjExact(vars[i])));
        }
    }

    /* add constraints of blocks to subMIPs */
    for (int i = 0; i < nconss; i++)
    {
        int nconsvars;
        int block = conslabels[i];
        assert(block < this->nblocks); /* we assume consecutive labels beginning with zero */

        /* skip linking constraints */
        if (block < 0)
            continue;

        nconsvars = SCIPgetNVarsExactLinear(this->origscip, conss[i]);

        consvals = SCIPgetValsExactLinear(this->origscip, conss[i]);
        SCIP_CALL(SCIPgetConsVars(this->origscip, conss[i], consvars, nconsvars, &success));

        /* create dummy constraint */
        sprintf(name, "%s", SCIPconsGetName(conss[i]));
        SCIP_CALL(SCIPcreateConsBasicExactLinear(this->subMIPs[block], &newcons, name, 0, NULL, NULL,
                                           SCIPgetLhsExactLinear(this->origscip, conss[i]), SCIPgetRhsExactLinear(this->origscip, conss[i])));

        /* add vars to dummy constraint */
        for (int v = 0; v < nconsvars; v++)
        {
            SCIPaddCoefExactLinear(this->subMIPs[block],
                                newcons,
                                (SCIP_VAR *)SCIPhashmapGetImage(this->varsmaps[block], (void *)consvars[v]),
                                consvals[v]);
        }

        SCIP_CALL(SCIPaddCons(this->subMIPs[block], newcons));
        SCIP_CALL(SCIPreleaseCons(this->subMIPs[block], &newcons));
    }

    int linkcounter = 0;
    linkingsign.resize(this->nlinking + 1);
    linkingpartsorig.resize(this->nlinking + 1);
    linkingpartsblock.resize(this->nblocks);
    for (int b = 0; b < this->nblocks; b++)
    {
        linkingpartsblock[b].resize(this->nlinking + 1);
    }

    /* add part of linking constraints to subMIPs and origscip */
    for (int i = 0; i < nconss; i++)
    {
        int nconsvars;

        assert(conslabels[i] < this->nblocks); /* we assume consecutive labels beginning with zero */
        /* skip block constraints */
        if (conslabels[i] >= 0)
            continue;
        assert(conslabels[i] == SCIP_DECOMP_LINKCONS);

        /* create dummy constraint */
        for (int b = 0; b < this->nblocks; b++)
        {
            sprintf(name, "%s_block_%d", SCIPconsGetName(conss[i]), b);
            SCIP_CALL(SCIPcreateConsBasicExactLinear(this->subMIPs[b], &newconss[b], name, 0, NULL, NULL,
                                                neginf, posinf));
            SCIP_CALL(SCIPcreateConsBasicExactLinear(this->origscip, &newconssorig[b], name, 0, NULL, NULL,
                                                neginf, posinf));
        }

        nconsvars = SCIPgetNVarsExactLinear(this->origscip, conss[i]);
        SCIP_CALL(SCIPgetConsVars(this->origscip, conss[i], consvars, nconsvars, &success));
        consvals = SCIPgetValsExactLinear(this->origscip, conss[i]);
        /* add vars to dummy constraint */
        for (int v = 0; v < nconsvars; v++)
        {
            for (int b = 0; b < this->nblocks; b++)
            {
                if (SCIPhashmapExists(this->varsmaps[b], (void *)consvars[v]))
                {
                    SCIPaddCoefExactLinear(this->subMIPs[b],
                                    newconss[b],
                                    (SCIP_VAR *)SCIPhashmapGetImage(this->varsmaps[b], (void *)consvars[v]),
                                    consvals[v]);
                    SCIPaddCoefExactLinear(this->origscip,
                                    newconssorig[b],
                                    consvars[v],
                                    consvals[v]);
                    break;
                }
            }
        }

        /* add constraint */
        for (int b = 0; b < this->nblocks; b++)
        {
            SCIP_CALL(SCIPaddCons(this->subMIPs[b], newconss[b]));
            linkingpartsblock[b][linkcounter] = newconss[b];
            SCIP_CALL(SCIPreleaseCons(this->subMIPs[b], &newconss[b]));
            SCIP_CALL(SCIPaddCons(this->origscip, newconssorig[b]));
            linkingpartsorig[linkcounter].push_back(newconssorig[b]);
            SCIP_CALL(SCIPreleaseCons(this->origscip, &newconssorig[b]));
        }
        assert(linkingpartsorig[linkcounter].size() == this->nblocks);

        if (!RatIsInfinity(SCIPgetRhsExactLinear(this->origscip, conss[i])))
        {
            if (!RatIsNegInfinity(SCIPgetLhsExactLinear(this->origscip, conss[i])))
            {
                assert(RatIsEqual(SCIPgetLhsExactLinear(this->origscip, conss[i]), SCIPgetRhsExactLinear(this->origscip, conss[i])));
                this->linkingsign[linkcounter] = 0;
            }
            else
            {
                this->linkingsign[linkcounter] = 1;
            }
        }
        else
        {
            assert(!RatIsNegInfinity(SCIPgetLhsExactLinear(this->origscip, conss[i])));
            this->linkingsign[linkcounter] = 2;
        }

        assert(success);
        linkcounter++;
    }
    assert(linkcounter == this->nlinking);

    /* add part of objective constraint to subMIPs and origscip and add event handler */
    for (int b = 0; b < this->nblocks; b++)
    {
        int nblockvars = SCIPgetNVars(this->subMIPs[b]);
        SCIP_VAR **blockvars = SCIPgetVars(this->subMIPs[b]);

        /* create dummy constraint */
        sprintf(name, "obj_block_%d", b);
        SCIP_CALL(SCIPcreateConsBasicExactLinear(this->subMIPs[b], &newconss[b], name, 0, NULL, NULL,
                                            neginf, posinf));
        SCIP_CALL(SCIPcreateConsBasicExactLinear(this->origscip, &newconssorig[b], name, 0, NULL, NULL,
                                            neginf, posinf));

        /* add vars to dummy constraint */
        for (int v = 0; v < nblockvars; v++)
        {
            SCIPaddCoefExactLinear(this->subMIPs[b],
                            newconss[b],
                            blockvars[v],
                            SCIPvarGetObjExact(blockvars[v]));
            SCIPaddCoefExactLinear(this->origscip,
                            newconssorig[b],
                            SCIPfindVar(this->origscip, SCIPvarGetName(blockvars[v])),
                            SCIPvarGetObjExact(blockvars[v]));
            assert(RatIsEqual(SCIPvarGetObjExact(blockvars[v]), SCIPvarGetObjExact(SCIPfindVar(this->origscip, SCIPvarGetName(blockvars[v])))));
        }

        /* add constraint */
        SCIP_CALL(SCIPaddCons(this->subMIPs[b], newconss[b]));
        linkingpartsblock[b][linkcounter] = newconss[b];
        SCIP_CALL(SCIPreleaseCons(this->subMIPs[b], &newconss[b]));
        SCIP_CALL(SCIPaddCons(this->origscip, newconssorig[b]));
        linkingpartsorig[linkcounter].push_back(newconssorig[b]);
        SCIP_CALL(SCIPreleaseCons(this->origscip, &newconssorig[b]));

        this->linkingsign[linkcounter] = 2;

    }
    linkcounter++;

    /* change type to continuous */
    for (int v = nvars - SCIPgetNContVars(this->origscip) - 1; v >= 0; v--)
    {
        SCIPchgVarType(this->origscip, vars[v], SCIP_VARTYPE_CONTINUOUS, &success);
        assert(!success);
    }
    assert(SCIPgetNContVars(this->origscip) == SCIPgetNVars(this->origscip));

    /* free memory */
    SCIPfreeBufferArrayNull(this->origscip, &conss);
    SCIPfreeBufferArray(this->origscip, &consvars);
    SCIPfreeBufferArray(this->origscip, &conslabels);

    RatFreeBuffer(SCIPbuffer(this->origscip), &neginf);
    RatFreeBuffer(SCIPbuffer(this->origscip), &posinf);

    return SCIP_OKAY;
}

SCIP_RETCODE Problem::addroot()
{
    Node *node = new Node(this->origscip, this->nblocks, this->nlinking);

    for (int i = 0; i < this->nlinking + 1; i++)
    {
        for (int k = 0; k < this->nblocks; k++)
        {
            RatSetString((node->rhs[i])[k], "inf");
            RatSetString((node->lhs[i])[k], "-inf");
        }
    }
    node->depth = 0;
    node->idx = 0;
    node->parent = NULL;
    node->status = NODE_STATUS_OPEN;

    this->nodes.push_back(node);
    this->nnodes++;

    return SCIP_OKAY;
}

SCIP_RETCODE Problem::freenodes()
{
    while (this->nodes.size() > 0)
    {
        Node *node = this->nodes.back() ;

        delete node;
        this->nodes.erase(this->nodes.end()-1);
        this->nnodes--;
    }

    return SCIP_OKAY;
}

/* main part of decomposition branching
 *
 * selects node, branches, cuts off
 */
SCIP_RETCODE Problem::run(time_point<std::chrono::system_clock> t_run_start)
{
    int solving_time_seconds;
    time_point<std::chrono::system_clock> t_run_end;
    bool timelimit = false;
    bool nodelimit = false;
    Node *node;
    SCIP_Rational* tmp;
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &tmp) );

    node = selectNode(); /* select first node (root) */

    printf("   time | node | depth | primalbound | node status\n");
    while (node != NULL)
    {
        /* check nodelimit */
        if (node->idx > this->maxnodes)
        {
            nodelimit = true;
            break;
        }

        /* check timelimit */
        t_run_end = system_clock::now();
        solving_time_seconds = (std::chrono::duration_cast<std::chrono::milliseconds>(t_run_end - t_run_start).count()) / 1000.0;
        if (solving_time_seconds >= this->maxtime)
        {
            timelimit = true;
            break;
        }

        printf("%5ds | %4d | %3d | ", solving_time_seconds, node->idx, node->depth);

        /* update and solve LP at current node */
#ifdef PRINT_SUBMIP_INFO
        printf("Update and solve LP ...\n");
#endif
        updateLP(node);
        SCIPsolve(this->origscip);

        /* handle node */
        switch (SCIPgetStatus(this->origscip))
        {
        case SCIP_STATUS_INFEASIBLE:
            RatPrintf("%q | prune by infeasibility\n", this->incumbent);
            node->status = NODE_STATUS_INFEASIBLE;
            break;
        case SCIP_STATUS_OPTIMAL:
            assert(SCIPisExactSolve(this->origscip));
            SCIPgetPrimalboundExact(this->origscip, tmp);
            /* primalbound >= incumbent */
            if (RatIsGE(tmp, this->incumbent))
            {
                RatPrintf("%q | prune by bound\n", this->incumbent);
                node->status = NODE_STATUS_PRUNEBOUND;
                break;
            }
            handlenode(node, &node->status);
            assert(node->status == NODE_STATUS_BRANCHED || node->status == NODE_STATUS_OPTIMAL);
            break;
        /* todo: handle suboptimal solutions */
        default:
            node->status = NODE_STATUS_INVALID;
            printf("######## ERROR! Node LP returned invalid status! ########\n");
            break;
        }

        SCIPfreeTransform(this->origscip);

        /* select next node */
        node = selectNode();
    }

    if (nodelimit)
    {
        printf("Maximal number of nodes reached! node idx = %d Exit!\n", node != NULL ? node->idx : -1);
    }
    else if (timelimit)
    {
        printf("Timelimit reached! node idx = %d Exit!\n", node != NULL ? node->idx : -1);
    }
    else
    {
        printf("No open node! node idx = %d Exit!\n", node != NULL ? node->idx : -1);
    }

    printf("Total Nodes: %d\n", this->nnodes);
    RatPrintf("Best found solution: %q\nnumber solutions found: %d\n", this->incumbent, this->solutionstorage.size());

    RatFreeBuffer(SCIPbuffer(this->origscip), &tmp);
    return SCIP_OKAY;
}

/* selects next open node */
Node *Problem::selectNode()
{
    assert(this->nnodes == this->nodes.size());

    int selectmethod = 0;
    /*
        0: last open node
        1: first open node
    */

    switch (selectmethod)
    {
    case 0:
        /* take last open node; depth-first search */
        for (int i = this->nnodes - 1; i >= 0; i--)
        {
            if (this->nodes[i]->status == NODE_STATUS_OPEN)
            {
                return this->nodes[i];
            }
        }
        break;
    case 1:
        /* take first open node; breadth-first search */
        for (int i = 0; i < this->nnodes; i++)
        {
            if (this->nodes[i]->status == NODE_STATUS_OPEN)
            {
                return this->nodes[i];
            }
        }
        break;
    default:
        printf("######## ERROR! ########\n");
        break;
    }

    return NULL;
}

/* updates rhs and lhs of parts of linking constraints */
void Problem::updateLP(Node *node)
{
    for (int i = 0; i < this->nlinking + 1; i++)
    {
        for (int b = 0; b < this->nblocks; b++)
        {
            assert(RatIsLE(SCIPgetLhsExactLinear(this->origscip, this->linkingpartsorig[i][b]), SCIPgetRhsExactLinear(this->origscip, this->linkingpartsorig[i][b])));
            if ( !RatIsEqual(node->rhs[i][b], SCIPgetRhsExactLinear(this->origscip, this->linkingpartsorig[i][b])))
            {
                SCIPchgRhsExactLinear(this->origscip, this->linkingpartsorig[i][b], node->rhs[i][b]);
            }

            if ( !RatIsEqual(node->lhs[i][b], SCIPgetLhsExactLinear(this->origscip, this->linkingpartsorig[i][b])))
            {
                SCIPchgLhsExactLinear(this->origscip, this->linkingpartsorig[i][b], node->lhs[i][b]);
            }
            assert(RatIsLE(node->lhs[i][b], node->rhs[i][b]));
        }
    }
#ifdef PRINT_SUBMIP_INFO
    printf("updated LP\n");
    SCIPprintOrigProblem(this->origscip, NULL, "cip", FALSE);
#endif
}

/* update submip of block with current node info and LP solution */
SCIP_RETCODE Problem::updatesubMIP(SCIP *subMIP, Node *node, SCIP_SOL *sublpsol, int block)
{
    SCIP_CONS *conspart;
    SCIP_Rational *activity;
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &activity) );

#ifdef PRINT_SUBMIP_INFO
    printf("Update subMIP ...\n");
#endif

    for (int i = 0; i < this->nlinking; i++) /* do not update constraint corresponding to objective function */
    {
        conspart = this->linkingpartsblock[block][i];

        /* calculate activity */
        SCIPgetActivityExactLinear(subMIP, conspart, sublpsol, activity);

        assert(RatIsGE(activity, node->lhs[i][block])); /* otherwise solution is not feasible for LP of current node */
        assert(RatIsLE(activity, node->rhs[i][block]));

        /* equation */
        if (linkingsign[i] == 0)
        {
            assert(false); /* todo: complete implementation for equations */
            SCIPchgRhsExactLinear(subMIP, conspart, activity);
            SCIPchgLhsExactLinear(subMIP, conspart, activity);
        }
        /* less equal Ax <= b */
        else if (linkingsign[i] == 1)
        {
            SCIPchgRhsExactLinear(subMIP, conspart, activity);
            SCIPchgLhsExactLinear(subMIP, conspart, node->lhs[i][block]);
        }
        /* greater equal Ax >= b */
        else
        {
            assert(linkingsign[i] == 2);
            SCIPchgLhsExactLinear(subMIP, conspart, activity);
            SCIPchgRhsExactLinear(subMIP, conspart, node->rhs[i][block]);
        }
    }

    /* copy sides from node for objective */
    conspart = this->linkingpartsblock[block][this->nlinking];
    SCIPgetActivityExactLinear(subMIP, conspart, sublpsol, activity);
    assert(RatIsGE(activity, node->lhs[this->nlinking][block])); /* otherwise solution is not feasible for LP of current node */
    assert(RatIsLE(activity, node->rhs[this->nlinking][block]));

    /* equation */
    if (linkingsign[this->nlinking] == 0)
    {
        assert(false); /* todo: complete implementation for equations */
    }
    /* less equal Ax <= b */
    else if (linkingsign[this->nlinking] == 1)
    {
        SCIPchgRhsExactLinear(subMIP, conspart, node->rhs[this->nlinking][block]);
        SCIPchgLhsExactLinear(subMIP, conspart, node->lhs[this->nlinking][block]);
    }
    /* greater equal Ax >= b */
    else
    {
        assert(linkingsign[this->nlinking] == 2);
        SCIPchgLhsExactLinear(subMIP, conspart, node->lhs[this->nlinking][block]);
        SCIPchgRhsExactLinear(subMIP, conspart, node->rhs[this->nlinking][block]);
    }
    RatFreeBuffer(SCIPbuffer(this->origscip), &activity);
#ifdef PRINT_SUBMIP_INFO
    SCIPprintOrigProblem(subMIP, NULL, "cip", FALSE);
#endif
    return SCIP_OKAY;
}

/* branches and adds new nodes */
SCIP_RETCODE Problem::branch(Node *parentnode, SCIP *submip, SCIP_Rational *blocksolval, SCIP_SOL *sublpsol, int block)
{
    SCIP_Rational* tmp;
    SCIP_Rational *activity;
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &tmp) );
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &activity) );

    /* new node for objective function */
    if (!RatIsInfinity(blocksolval) && !RatIsNegInfinity(blocksolval))
    {
        Node *node = new Node(this->origscip, this->nblocks, this->nlinking);

        /* copy sides of parent node */
        for (int i = 0; i < this->nlinking + 1; i++)
        {
            for (int k = 0; k < this->nblocks; k++)
            {
                RatSet(node->rhs[i][k], parentnode->rhs[i][k]);
                RatSet(node->lhs[i][k], parentnode->lhs[i][k]);
            }
        }
        /* update side for objective function */
        assert(SCIPgetObjsense(this->origscip) == SCIP_OBJSENSE_MINIMIZE);
        assert(RatIsLE(parentnode->lhs[this->nlinking][block], blocksolval));

        if (RatIsZero(this->delta))
            RatSet(node->lhs[this->nlinking][block], blocksolval); /* no epsilon necessary */
        else
            deltaceil(this->origscip, blocksolval, this->delta, node->lhs[this->nlinking][block]); /* use of delta; no strict rounding */

        node->depth = parentnode->depth + 1;
        node->idx = this->nnodes;
        node->parent = parentnode;
        node->status = NODE_STATUS_OPEN;

        this->nodes.push_back(node);
        this->nnodes++;

        parentnode->children[this->nlinking] = node;
    }
    else
    {
        parentnode->children[this->nlinking] = NULL;
    }

    /* new node for each linking constraint */
    for (int i = 0; i < this->nlinking; i++)
    {
        Node *node = new Node(this->origscip, this->nblocks, this->nlinking);

        /* copy sides of parent node */
        for (int j = 0; j < this->nlinking + 1; j++)
        {
            for (int k = 0; k < this->nblocks; k++)
            {
                RatSet(node->rhs[j][k], parentnode->rhs[j][k]);
                RatSet(node->lhs[j][k], parentnode->lhs[j][k]);
            }
        }

        /* update side for linking constraint */
        if (this->linkingsign[i] == 1)
        {
            SCIPgetActivityExactLinear(submip, this->linkingpartsblock[block][i], sublpsol, activity);
            if (RatIsZero(this->delta))
            {
                RatAdd(node->lhs[i][block], activity, this->epsilon); /* use of epsilon */
            }
            else
                deltaceilstrict(this->origscip, activity, this->delta, node->lhs[i][block]); /* use of delta */
        }
        else if (this->linkingsign[i] == 2)
        {
            SCIPgetActivityExactLinear(submip, this->linkingpartsblock[block][i], sublpsol, activity);
            if (RatIsZero(this->delta))
                RatDiff(node->rhs[i][block], activity, this->epsilon); /* use of epsilon */
            else
                deltafloorstrict(this->origscip, activity, this->delta, node->rhs[i][block]); /* use of delta */
        }
        else
        {
            /* linking constraint is equation, not fully implemented */
            assert(false);
        }

        if (RatIsGT(node->lhs[i][block], node->rhs[i][block]))
        {
            /* node would be infeasible -> do not add */
            parentnode->children[i] = NULL;
            delete node;
            continue;
        }

        /* add opposite of prior constraints */
        for (int j = 0; j < i; j++)
        {
            if (this->linkingsign[j] == 1)
            {
                SCIPgetActivityExactLinear(submip, this->linkingpartsblock[block][j], sublpsol, activity);
                RatSet(node->rhs[j][block], activity); /* no epsilon necessary */
            }
            else if (this->linkingsign[j] == 2)
            {
                SCIPgetActivityExactLinear(submip, this->linkingpartsblock[block][j], sublpsol, activity);
                RatSet(node->lhs[j][block], activity); /* no epsilon necessary */
            }
            else
            {
                /* linking constraint is equation, not fully implemented */
                assert(false);
            }
            assert(RatIsLE(node->lhs[j][block], node->rhs[j][block]));
        }
        if (parentnode->children[this->nlinking] != NULL)
        {
            /* opposite of objective function only if node was added */
            if (RatIsZero(this->delta))
                RatDiff(node->rhs[this->nlinking][block], blocksolval, this->epsilon); /* use of epsilon */
            else
                deltafloorstrict(this->origscip, blocksolval, this->delta, node->rhs[this->nlinking][block]); /* use of delta */

            assert(RatIsLE(node->lhs[this->nlinking][block], node->rhs[this->nlinking][block]));
        }

        node->depth = parentnode->depth + 1;
        node->idx = this->nnodes;
        node->parent = parentnode;
        node->status = NODE_STATUS_OPEN;

        this->nodes.push_back(node);
        this->nnodes++;

        parentnode->children[i] = node;
    }
    RatFreeBuffer(SCIPbuffer(this->origscip), &activity);
    RatFreeBuffer(SCIPbuffer(this->origscip), &tmp);
    return SCIP_OKAY;
}

/* handles current node */
SCIP_RETCODE Problem::handlenode(Node *node, NodeStatus *status)
{
    SCIP_SOL *lpsol;
    SCIP_SOL *blocksols[this->nblocks];
    SCIP_SOL *sublpsols[this->nblocks];
    SCIP_Rational **sublpsolvals; /* value of subsolution */
    SCIP_Rational **blocksolvals; /* value of subsolution */
    vector<int> branchcands;      /* idx of blocks that are branching candidates */
    bool intsolfound = true;
    bool branched = false;
    SCIP_Rational* tmp;
    SCIP_CALL( RatCreateBufferArray(SCIPbuffer(this->origscip), &sublpsolvals, this->nblocks) );
    SCIP_CALL( RatCreateBufferArray(SCIPbuffer(this->origscip), &blocksolvals, this->nblocks) );
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &tmp) );

#ifdef PRINT_SUBMIP_INFO
    printf("Check and solve blockproblems ...\n");
#endif

    for (int b = this->nblocks-1; b >=0; b--)
    {
        sublpsols[b] = NULL;
        blocksols[b] = NULL;
    }

    lpsol = SCIPgetBestSol(this->origscip);
    assert(SCIPisExactSol(this->origscip, lpsol));

#ifdef PRINT_SUBMIP_INFO
    SCIPprintSolExact(this->origscip, lpsol, NULL, FALSE);
#endif

    /* for each block, check if integer var with fractional value, solve subMIP */
    for (int b = 0; b < this->nblocks; b++)
    {
        SCIP_VAR *origvar;
        SCIP_VAR *subvar;
        SCIP_Rational *lpsolval; /* one single variable */
        SCIP_CALL(RatCreateBuffer(SCIPbuffer(this->origscip), &lpsolval));
        int nentries;
        bool fractionalblock = false;

        SCIP_CALL(SCIPfreeTransform(this->subMIPs[b]));

        SCIP_CALL(SCIPcreateSolExact(this->subMIPs[b], &sublpsols[b], NULL));
        assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));

        nentries = SCIPhashmapGetNEntries(this->varsmaps[b]);

        /* check solution if integral, and store subsolution */
        for (int e = 0; e < nentries; ++e)
        {
            SCIP_HASHMAPENTRY *entry;
            entry = SCIPhashmapGetEntry(this->varsmaps[b], e);

            if (entry != NULL)
            {
                origvar = (SCIP_VAR *)SCIPhashmapEntryGetOrigin(entry);
                subvar = (SCIP_VAR *)SCIPhashmapEntryGetImage(entry);

                /* create lp sol corresponding to block */
                SCIPgetSolValExact(this->origscip, lpsol, origvar, lpsolval);

                SCIP_CALL(SCIPsetSolVal(this->subMIPs[b], sublpsols[b], subvar, RatApproxReal(lpsolval)));
                SCIPsetSolValExact(this->subMIPs[b], sublpsols[b], subvar, lpsolval);

                /* check if integer var with fractional lp sol */
                if (SCIPvarGetType(subvar) != SCIP_VARTYPE_CONTINUOUS)
                {
                    if (!RatIsIntegral(lpsolval))
                    {
                        fractionalblock = true;
                    }
                }
            }
        }
        assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));
        SCIPgetSolOrigObjExact(this->subMIPs[b], sublpsols[b], sublpsolvals[b]);

        RatFreeBuffer(SCIPbuffer(this->origscip), &lpsolval);

        /* update and solve submip; store integer subsolution */
        if (fractionalblock)
        {
            assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));
            updatesubMIP(this->subMIPs[b], node, sublpsols[b], b);
            assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));

            SCIP_CALL(SCIPsolve(this->subMIPs[b]));

            blocksols[b] = NULL;
            assert(SCIPgetObjsense(this->subMIPs[b]) == SCIP_OBJSENSE_MINIMIZE);

            switch (SCIPgetStatus(this->subMIPs[b]))
            {
            case SCIP_STATUS_INFEASIBLE:
#ifdef PRINT_SUBMIP_INFO
                printf("Submip is infeasible!\n");
#endif
                RatSetString(blocksolvals[b], "inf");
                intsolfound = false;
                break;
            case SCIP_STATUS_UNBOUNDED:
#ifdef PRINT_SUBMIP_INFO
                printf("Submip is unbounded!\n");
#endif
                RatSetString(blocksolvals[b], "-inf");
                intsolfound = false;
                break;
            case SCIP_STATUS_OPTIMAL:
                blocksols[b] = SCIPgetBestSol(this->subMIPs[b]);
                assert(SCIPisExactSol(this->subMIPs[b], blocksols[b]));
                SCIPgetPrimalboundExact(this->subMIPs[b], blocksolvals[b]);
#ifdef PRINT_SUBMIP_INFO
                RatPrintf("Submip optimal solved with solval %q!\n", blocksolvals[b]);
                SCIPprintSolExact(this->subMIPs[b], blocksols[b], NULL, FALSE);
#endif
                break;
            /* todo: handle suboptimal solutions */
            default:
                printf("######## ERROR! Submip returned invalid status! ########\n");
                intsolfound = false;
                break;
            }
        }
        else
        {
#ifdef PRINT_SUBMIP_INFO
            printf("Submip is already integer!\n");
#endif
            blocksols[b] = sublpsols[b]; /* set integer solution */
            RatSet(blocksolvals[b], sublpsolvals[b]);
            assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));
        }
        assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));

        /* check if worse solution */
        /* sublpsolval < blocksolval */
        if (!RatIsZero(this->delta))
        {
            deltafloorstrict(this->origscip, blocksolvals[b], this->delta, tmp);
        }

        if ((RatIsZero(this->delta) && RatIsLT(sublpsolvals[b], blocksolvals[b]))
            || ( !RatIsZero(this->delta) && RatIsLE(sublpsolvals[b], tmp))) /* use of delta */
        {
            /* store branching candidates */
            branchcands.push_back(b);

            /* break if we have a branching candidate, and if we can not find an integer solution or have already an incumbent */
            if (!intsolfound || this->solutionstorage.size() >= 1)
            {
                if (b < this->nblocks - 1)
                    intsolfound = false; /* set value to false since not all blocks are checked */
                break;
            }
        }
        else
        {
            assert((RatIsZero(this->delta) && RatIsEqual(sublpsolvals[b], blocksolvals[b]))
                || (!RatIsZero(this->delta) && RatIsLE(sublpsolvals[b], blocksolvals[b])));
        }
        assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));
        assert(SCIPisExactSol(this->subMIPs[b], blocksols[b]));
    }

    /* branch and add new nodes */
    if (branchcands.size() >= 1)
    {
        int branchblock = branchcands[0]; /* block of selected branching candidate (first candidate) */
        RatPrintf("%q | branch on block %d\n", this->incumbent, branchblock);
        assert(SCIPisExactSol(this->subMIPs[branchblock], sublpsols[branchblock]));
        branch(node, this->subMIPs[branchblock], blocksolvals[branchblock], sublpsols[branchblock], branchblock);
        branched = true;
    }

    /* if we reach this part of the code, we found an integer optimal solution for the current node */
    if (intsolfound)
    {
        SCIPfreeTransform(this->origscip);

        SCIP_SOL *intsol;
        SCIPcreateSolExact(this->origscip, &intsol, NULL);
        for (int b = 0; b < this->nblocks; b++)
        {
#ifdef PRINT_SUBMIP_INFO
            SCIPprintSol(this->subMIPs[b], blocksols[b], NULL, false);
            SCIPprintSolExact(this->subMIPs[b], blocksols[b], NULL, false);
#endif
            assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));
            int nentries = SCIPhashmapGetNEntries(this->varsmaps[b]);
            SCIP_VAR *origvar;
            SCIP_VAR *subvar;

            for (int e = 0; e < nentries; ++e)
            {
                SCIP_HASHMAPENTRY *entry;
                entry = SCIPhashmapGetEntry(this->varsmaps[b], e);

                if (entry != NULL)
                {
                    origvar = (SCIP_VAR *)SCIPhashmapEntryGetOrigin(entry);
                    subvar = (SCIP_VAR *)SCIPhashmapEntryGetImage(entry);
                    SCIPgetSolValExact(this->subMIPs[b], blocksols[b], subvar, tmp);

                    SCIPsetSolVal(this->origscip, intsol, origvar, RatApproxReal(tmp));
                    SCIPsetSolValExact(this->origscip, intsol, origvar, tmp);
                }
            }
            assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));
        }
        this->solutionstorage.push_back(intsol);
        assert(intsol != NULL);
        assert(SCIPisExactSolve(this->origscip));
        assert(SCIPisExactSol(this->origscip, intsol));
        assert(SCIPisExactSol(this->subMIPs[this->nblocks-1], sublpsols[this->nblocks-1]));

        SCIPgetSolOrigObjExact(this->origscip, intsol, tmp);
        if ( RatIsInfinity(this->incumbent) || RatIsGE(this->incumbent, tmp) )
        {
            SCIPgetSolOrigObjExact(this->origscip, intsol, this->incumbent);
            this->DBsol = intsol;
        }
        RatPrintf("%q | integer solution found (approx. %e)\n", this->incumbent, RatApproxReal(this->incumbent));
        SCIPprintSolExact(this->origscip, intsol, NULL, FALSE);
    }

    if(branched)
    {
        *status = NODE_STATUS_BRANCHED;
    }
    else
    {
        assert(intsolfound);
        *status = NODE_STATUS_OPTIMAL;
    }

    for (int b = this->nblocks-1; b >=0; b--)
    {
        if(sublpsols[b] != NULL)
        {
            assert(SCIPisExactSol(this->subMIPs[b], sublpsols[b]));
            SCIPfreeSol(this->subMIPs[b], &sublpsols[b]);
        }
    }
    RatFreeBuffer(SCIPbuffer(this->origscip), &tmp);
    RatFreeBufferArray(SCIPbuffer(this->origscip), &blocksolvals, this->nblocks);
    RatFreeBufferArray(SCIPbuffer(this->origscip), &sublpsolvals, this->nblocks);

    return SCIP_OKAY;
}

SCIP_RETCODE Problem::checksol()
{
    printf("check found solution ...\n");
    SCIP_SOL *copysol;
    SCIP_SOL *bestsol;
    SCIP_Rational* tmp;
    SCIP_CALL( RatCreateBuffer(SCIPbuffer(this->origscip), &tmp) );

    SCIPprintSolExact(this->origscip, this->DBsol, NULL, false);
    SCIP_CALL(SCIPcreateSol(this->scipcopy, &copysol, NULL)); /* not exact since exact solutions with negated vars can not get checked */

    int nvars = SCIPgetNVars(this->origscip);
    SCIP_VAR **vars = SCIPgetVars(this->origscip);

    for (int v = 0; v < nvars; v++)
    {
        SCIP_VAR *copyvar = SCIPfindVar(this->scipcopy, SCIPvarGetName(vars[v]));

        assert(copyvar != NULL);

        SCIPgetSolValExact(this->origscip, this->DBsol, vars[v], tmp);
        SCIP_CALL(SCIPsetSolVal(this->scipcopy, copysol, copyvar, RatApproxReal(tmp)));
    }

    assert(SCIPisEQ(this->origscip, RatApproxReal(this->incumbent), SCIPsolGetOrigObj(copysol)));
    SCIPgetSolOrigObjExact(this->origscip, this->DBsol, tmp);
    RatPrintf("%q %q %g \n", this->incumbent, tmp, SCIPsolGetOrigObj(this->DBsol));
    assert(RatIsEqual(this->incumbent, tmp));

    SCIPprintSol(this->scipcopy, copysol, NULL, false);
    SCIP_Bool stored;
    SCIP_CALL(SCIPcheckSol(this->scipcopy, copysol, true, false, true, true, true, &stored));
    printf("feasible %d\n", stored);
    SCIP_CALL(SCIPaddSol(this->scipcopy, copysol, &stored));
    printf("added %d\n", stored);
    printf("solve scipcopy\n");
    SCIPsolve(this->scipcopy);
    printf("Optimal solution of original problem:\n");
    bestsol = SCIPgetBestSol(this->scipcopy);
    SCIPprintSol(this->scipcopy, bestsol, NULL, false);

    RatFreeBuffer(SCIPbuffer(this->origscip), &tmp);

    return SCIP_OKAY;
}

/* free data */
SCIP_RETCODE Problem::free()
{
    for (int i = this->solutionstorage.size()-1; i >=0; i--)
    {
        SCIPfreeSol(this->origscip, &this->solutionstorage[i]);
    }

    if (size(this->varsmaps) != 0)
    {
        assert(size(this->varsmaps) == this->nblocks);
        for (int b = 0; b < this->nblocks; b++)
        {
                SCIPhashmapFree(&this->varsmaps[b]);
        }
    }

    for (int i = 0; i < this->subMIPs.size(); i++)
    {
        SCIP_CALL(SCIPfree(&this->subMIPs[i]));
    }

    SCIP_CALL(SCIPfree(&this->origscip));
    SCIP_CALL(SCIPfree(&this->scipcopy));

    return SCIP_OKAY;
}

/** main method starting program */
int main(
    int argc,   /**< number of arguments from the shell */
    char **argv /**< array of shell arguments */
)
{
    int timelimit = 3600; /* timelimit in seconds */
    int epsilonnom = 1;  /* epsilon = epsilonnom/epsilondenom */
    int epsilondenom = 1;
    const char *instancefile = NULL;
    const char *decfile = NULL;
    const char *metafile = NULL;
    Problem *problem = new Problem();

    printf("Start program!\n");
    time_point<std::chrono::system_clock> t_all_start = system_clock::now();

    if (argc <= 5)
    {
        printf("\nToo few arguments!\nUsage: %s timelimit epsilon-nom epsilon-denom .lp .dec (optional: .meta)\n", argv[0]);
        return 0;
    }
    else if (argc == 6 || argc == 7)
    {
        printf("\nNumber Of Arguments Passed: %d\n", argc - 1);
        printf("Arguments Passed:\n");
        timelimit = atoi(argv[1]);
        printf("timelimit: %d\n", timelimit);
        problem->settimelimit(timelimit);
        epsilonnom = atoi(argv[2]); /* enter epsilon as nom denom */
        epsilondenom = atoi(argv[3]);
        problem->setepsilon(epsilonnom, epsilondenom);
        instancefile = argv[4];
        printf("instance file: %s\n", instancefile);
        decfile = argv[5];
        printf("decomposition file: %s\n", decfile);
        if (argc == 7)
        {
            metafile = argv[6];
            printf("meta file: %s\n", metafile);
        }
        else
        {
            metafile = NULL;
        }
    }
    else if (argc >= 8)
    {
        printf("\nToo many arguments!\nUsage: %s timelimit epsilon-nom epsilon-denom .lp .dec (optional: .meta)\n", argv[0]);
        return 0;
    }

    problem->create(&instancefile, &decfile, &metafile);
    problem->createsubMIPs();
    problem->addroot();
    time_point<std::chrono::system_clock> t_run_start = system_clock::now();
    problem->run(t_run_start);
    time_point<std::chrono::system_clock> t_run_end = system_clock::now();

    /* ckeck solution */
    if (problem->DBsol != NULL)
        problem->checksol();

    /* free data */
    problem->freenodes();
    problem->free();
    delete problem;
    time_point<std::chrono::system_clock> t_all_end = system_clock::now();

    int total_time_milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(t_all_end - t_all_start).count();
    int solving_time_milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(t_run_end - t_run_start).count();
    printf("Total time (sec): %.2f\n", total_time_milliseconds / 1000.0);
    printf("Solving time (sec): %.2f\n", solving_time_milliseconds / 1000.0);

    printf("End program!\n");
    return 0;
}
