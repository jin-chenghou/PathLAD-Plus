#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <getopt.h>
#include <math.h>
#include <sys/time.h>
#include <sys/resource.h>

// define boolean type as char
#define true 1
#define false 0
#define bool char

// Global variables
int nbNodes = 1;      // number of nodes in the search tree
int nbFail = 0;       // number of failed nodes in the search tree
int nbSol = 0;        // number of solutions found
struct rusage ru;     // reusable structure to get CPU time usage

#include "compatibility.c"
#include "graph.c"
#include "domainsPath.c"
#include "allDiff.c"
#include "lad.c"


int sol[1500][6500];
int Sum[6500];

bool dense = false;

void qs(int q[], int l, int r, Tgraph* Gt, int b)
{
    if(l>=r) return;
    int i = l - 1, j = r + 1, x = Gt->nbAdj[q[l + r >> 1]] + sol[b][q[l + r >> 1]];
    int maxS = Sum[q[l + r >> 1]];
    while(i < j)
    {
        do i++; while(Gt->nbAdj[q[i]] + sol[b][q[i]] > x || (Gt->nbAdj[q[i]] + sol[b][q[i]]== x && Sum[q[i]] > maxS));
        do j--;  while(Gt->nbAdj[q[j]] + sol[b][q[j]] < x  || (Gt->nbAdj[q[j]] + sol[b][q[j]] == x && Sum[q[j]] < maxS));
        if(i < j) 
        {
            int t = q[i];
            q[i] = q[j];
            q[j] = t;
        }
    }
    qs(q,l,j,Gt,b);
    qs(q,j+1,r,Gt,b);
}

bool filter(bool induced, Tdomain* D, Tgraph* Gp, Tgraph* Gt){
    // filter domains of all vertices in D->toFilter wrt LAD and ensure GAC(allDiff)
    // return false if some domain becomes empty; true otherwise
    int u, v, i, oldNbVal;
    while (!toFilterEmpty(D)){
        while (!toFilterEmpty(D)){
            u=nextToFilter(D,Gp->nbVertices);
            oldNbVal = D->nbVal[u];
            i=D->firstVal[u];
            while (i<D->firstVal[u]+D->nbVal[u]){
                // for every target node v in D(u), check if G_(u,v) has a covering matching
                v=D->val[i];
                if (checkLAD(induced,u,v,D,Gp,Gt)) i++;
                else if (!removeValue(u,v,D,Gp,Gt)) return false;
            }
            if ((D->nbVal[u]==1) && (oldNbVal>1) && (!matchVertex(u,induced,D,Gp,Gt))) return false;
            if (D->nbVal[u]==0) return false;
        }
        if (!ensureGACallDiff(induced,Gp,Gt,D)) return false;
    }
    return true;
}

int restars = 0;

int L = 1;
int alldif = 0;
int Base = 500;
int bas = 10;
int uss = 0;
bool trans = false;
bool firstus = true;
int Nnode;
bool solve(int timeLimit, bool firstSol, bool induced, int verbose, Tdomain* D, Tgraph* Gp, Tgraph* Gt, int depth, bool absd){
    // if firstSol then search for the first solution; otherwise search for all solutions
    // if induced then search for induced subgraphs; otherwise search for partial subgraphs
    // return false if CPU time limit exceeded before the search is completed
    // return true otherwise
    if(nbSol > 0) return true;
    int u, v, nextVar, i;
    int nbVal[Gp->nbVertices];
    int globalMatching[Gp->nbVertices];
    if(depth == 0){
        nbFail = 0;
        nbNodes = 0;
    }
    bool us = true;
    nbNodes++;
    //printf("%d %d\n",depth,restars);
    getrusage(RUSAGE_SELF, &ru);
    if (ru.ru_utime.tv_sec >= timeLimit)
        // CPU time limit exceeded
        return false;
    if(dense) trans = true;
    if(!dense) trans = false;
    if(trans && ((nbNodes > 1000 && nbNodes * 0.85 < nbFail) || ru.ru_utime.tv_sec >= 180)) us = false;
    if(!us && firstus) {
        firstus = false;
        Nnode = nbNodes;
    }
    if (us && !filter(induced,D,Gp,Gt)){
        // filtering has detected an inconsistency
        alldif++;
        if (verbose == 2) printf("Filtering has detected an inconsistency\n");
        nbFail++;
        resetToFilter(D,Gp->nbVertices);
        return true;
    }

    bool Use = false;

    
    // The current node of the search tree is consistent wrt to LAD and GAC(allDiff)
    // Save domain sizes and global all different matching
    // and search for the non matched vertex nextVar with smallest domain
    memcpy(nbVal, D->nbVal, Gp->nbVertices*sizeof(int));
    memcpy(globalMatching, D->globalMatchingP, Gp->nbVertices*sizeof(int));
    nextVar=-1;
    int d = 0;
    int sum = 0;
    for (u=0; u<Gp->nbVertices; u++){
        if ((nbVal[u]>1) &&
            ((nextVar<0) ||
             (nbVal[u]<nbVal[nextVar]) || // search variable with min domain
             ((nbVal[u] == nbVal[nextVar]) && (Gp->nbAdj[u]>Gp->nbAdj[nextVar])))) // break ties with degree
            nextVar=u;
            if(nbVal[u] == 1) d++;
            //if(nbVal[u] == 1) printf("%d=%d ",u,D->val[D->firstVal[u]]);
            sum += nbVal[u] - 1;
    }
    //printf("%d %d %d \n",d,depth,alldif);
    //if(nextVar != -1) printf("%d\n",nbVal[nextVar]);
    if (nextVar==-1){// All vertices are matched => Solution found
        nbSol++;
        if (verbose >= 1){
            printf("Solution %d: ",nbSol);
            for (u=0; u<Gp->nbVertices; u++) printf("%d=%d ",u,D->val[D->firstVal[u]]);
            printf("\n");
        }
        //resetToFilter(D,Gp->nbVertices);
        return true;
    }
    
    // save the domain of nextVar to iterate on its values
    int val[D->nbVal[nextVar]];
    memcpy(val, &(D->val[D->firstVal[nextVar]]), D->nbVal[nextVar]*sizeof(int));
    
    // branch on nextVar=v, for every target node v in D(u)
    int cnts = 0;
    for(i=0; ((i<nbVal[nextVar]) && ((firstSol==0)||(nbSol==0))); i++) cnts++;

    int tmps[cnts + 1];
    memset(tmps,0,sizeof tmps);
    int idxs = 0;
    for(i=0; ((i<nbVal[nextVar]) && ((firstSol==0)||(nbSol==0))); i++) tmps[idxs++] = val[i];

    int sz = sizeof(tmps) / sizeof(tmps[0]);
    //for(int i = 0;i < idxs;i++) printf("%d ",Gt->nbAdj[tmps[i]]);
    
    qs(tmps,0,idxs - 1, Gt, nextVar);


    //for(int i = 0;i < idxs;i++) printf("%d ",Gt->nbAdj[tmps[i]]);
   // puts(" ");
   // puts(" ");
    if(!us && ((nbNodes > 2 * Nnode && nbNodes * 0.80 > nbFail) || ru.ru_utime.tv_sec > 600)){
        for(i=0; i < idxs;i++){
        v = tmps[i];
        if (verbose == 2) printf("Branch on %d=%d\n",nextVar,v);
        if ((!removeAllValuesButOnes(nextVar,v,D,Gp,Gt)) || (!matchVertexx(nextVar,induced,D,Gp,Gt))){
            if (verbose == 2) printf("Inconsistency detected while matching %d to %d\n",nextVar,v);
            nbFail++;
            nbNodes++;
            resetToFilter(D,Gp->nbVertices);
        }
        else {
            bool abd = true;
            if (!solve(timeLimit,firstSol,induced,verbose,D,Gp,Gt,depth + 1,abd)){
            // CPU time exceeded
            return false;}
            if(nbSol > 0) return true;
        }
        
        // restore domain sizes and global all different matching
        if(nbSol > 0) return true;
        if (verbose == 2) printf("End of branch %d=%d\n",nextVar,v);
        memset(D->globalMatchingT,-1,sizeof(int)*Gt->nbVertices);
        memcpy(D->nbVal, nbVal, Gp->nbVertices*sizeof(int));
        memcpy(D->globalMatchingP, globalMatching, Gp->nbVertices*sizeof(int));
        for (u=0; u<Gp->nbVertices; u++){
            D->globalMatchingT[globalMatching[u]] = u;
        }
    }
    }
    else{
    for(i=0; i < idxs;i++){
        v = tmps[i];
        if (verbose == 2) printf("Branch on %d=%d\n",nextVar,v);
        if ((!removeAllValuesButOne(nextVar,v,D,Gp,Gt)) || (!matchVertex(nextVar,induced,D,Gp,Gt))){
            if (verbose == 2) printf("Inconsistency detected while matching %d to %d\n",nextVar,v);
            nbFail++;
            nbNodes++;
            resetToFilter(D,Gp->nbVertices);
        }
        else {
            bool abd = false;
            if (!solve(timeLimit,firstSol,induced,verbose,D,Gp,Gt,depth + 1,abd)){
            // CPU time exceeded
            return false;}
            if(nbSol > 0) return true;
        }
        
        // restore domain sizes and global all different matching
        if(nbSol > 0) return true;
        if (verbose == 2) printf("End of branch %d=%d\n",nextVar,v);
        memset(D->globalMatchingT,-1,sizeof(int)*Gt->nbVertices);
        memcpy(D->nbVal, nbVal, Gp->nbVertices*sizeof(int));
        memcpy(D->globalMatchingP, globalMatching, Gp->nbVertices*sizeof(int));
        for (u=0; u<Gp->nbVertices; u++){
            D->globalMatchingT[globalMatching[u]] = u;
        }
    }
    }
    return true;
}

bool solves_pre(int timeLimit, bool firstSol, bool induced, int verbose, Tdomain* D, Tgraph* Gp, Tgraph* Gt, int depth, bool absd){
    if(nbSol > 0) return true;
    int u, v, nextVar, i;
    int nbVal[Gp->nbVertices];
    int globalMatching[Gp->nbVertices];
    nbNodes++;
    
    getrusage(RUSAGE_SELF, &ru);
    if (ru.ru_utime.tv_sec >= timeLimit)
        // CPU time limit exceeded
        return false;
    if (!filter(induced,D,Gp,Gt)){
        // filtering has detected an inconsistency
        if (verbose == 2) printf("Filtering has detected an inconsistency\n");
        nbFail++;
        resetToFilter(D,Gp->nbVertices);
        return true;
    }


    memcpy(nbVal, D->nbVal, Gp->nbVertices*sizeof(int));
    memcpy(globalMatching, D->globalMatchingP, Gp->nbVertices*sizeof(int));
    nextVar=-1;
    int d = 0;
    int sum = 0;
    for (u=0; u<Gp->nbVertices; u++){
        if ((nbVal[u]>1) &&
            ((nextVar<0) ||
             (nbVal[u]<nbVal[nextVar]) || // search variable with min domain
             ((nbVal[u] == nbVal[nextVar]) && (Gp->nbAdj[u]>Gp->nbAdj[nextVar])))) // break ties with degree
            nextVar=u;
            if(nbVal[u] == 1) d++;
            //if(nbVal[u] == 1) printf("%d=%d ",u,D->val[D->firstVal[u]]);
            sum += nbVal[u] - 1;
    }
    if (nextVar==-1){// All vertices are matched => Solution found
        nbSol++;
        if (verbose >= 1){
            printf("Solution %d: ",nbSol);
            for (u=0; u<Gp->nbVertices; u++) printf("%d=%d ",u,D->val[D->firstVal[u]]);
            printf("\n");
        }
        resetToFilter(D,Gp->nbVertices);
        return true;
    }
    
    // save the domain of nextVar to iterate on its values
    int val[D->nbVal[nextVar]];
    memcpy(val, &(D->val[D->firstVal[nextVar]]), D->nbVal[nextVar]*sizeof(int));
    
    // branch on nextVar=v, for every target node v in D(u)
    int cnts = 0;
    for(i=0; ((i<nbVal[nextVar]) && ((firstSol==0)||(nbSol==0))); i++) cnts++;

    int tmps[cnts + 1];
    memset(tmps,0,sizeof tmps);
    int idxs = 0;
    for(i=0; ((i<nbVal[nextVar]) && ((firstSol==0)||(nbSol==0))); i++) tmps[idxs++] = val[i];

    int sz = sizeof(tmps) / sizeof(tmps[0]);
    for(i = 0;i < idxs;i++) sol[nextVar][tmps[i]]++;
    for(i=0; i < idxs;i++){
        v = tmps[i];
        if ((!removeAllValuesButOne(nextVar,v,D,Gp,Gt)) || (!matchVertex(nextVar,induced,D,Gp,Gt))){
            if (verbose == 2) printf("Inconsistency detected while matching %d to %d\n",nextVar,v);
            nbFail++;
            nbNodes++;
            resetToFilter(D,Gp->nbVertices);
        }
        else {
            if (!solves_pre(timeLimit,firstSol,induced,verbose,D,Gp,Gt,depth + 1,0)){
            // CPU time exceeded
             //resetToFilter(D,Gp->nbVertices);
             
             memset(D->globalMatchingT,-1,sizeof(int)*Gt->nbVertices);
             memcpy(D->nbVal, nbVal, Gp->nbVertices*sizeof(int));
             memcpy(D->globalMatchingP, globalMatching, Gp->nbVertices*sizeof(int));
             for (u=0; u<Gp->nbVertices; u++){
                D->globalMatchingT[globalMatching[u]] = u;
            }

            return false;}

            if(nbSol > 0) return true;
    
            
        }
        
        // restore domain sizes and global all different matching
        if(nbSol > 0) return true;
        if (verbose == 2) printf("End of branch %d=%d\n",nextVar,v);
        memset(D->globalMatchingT,-1,sizeof(int)*Gt->nbVertices);
        memcpy(D->nbVal, nbVal, Gp->nbVertices*sizeof(int));
        memcpy(D->globalMatchingP, globalMatching, Gp->nbVertices*sizeof(int));
        for (u=0; u<Gp->nbVertices; u++){
            D->globalMatchingT[globalMatching[u]] = u;
        }
    }
    return true;
}

void disorganise(int a[], int len)
{
    srand( time(NULL) );
    int rN1 = (rand() % len);
    int rN2 = (rand() % len);
    for (int i = 0; i < len + 2; i++) {
        if (rN1 != rN2) {
            exc(&a[rN1], &a[rN2]);
        }
        rN1 = (rand() % len);
        rN2 = (rand() % len);
    }
}

void exc(int* a, int* b)
{
    int t;
    t = *a;
    *a = *b;
    *b = t;
}


bool solves_pres(int timeLimit, bool firstSol, bool induced, int verbose, Tdomain* D, Tgraph* Gp, Tgraph* Gt, int depth, bool absd){
    if(nbSol > 0) return true;
    int u, v, nextVar, i;
    int nbVal[Gp->nbVertices];
    int globalMatching[Gp->nbVertices];
    nbNodes++;
    
    getrusage(RUSAGE_SELF, &ru);
    if (ru.ru_utime.tv_sec >= timeLimit)
        // CPU time limit exceeded
        return false;
    if (!filter(induced,D,Gp,Gt)){
        // filtering has detected an inconsistency
        if (verbose == 2) printf("Filtering has detected an inconsistency\n");
        nbFail++;
        resetToFilter(D,Gp->nbVertices);
        return true;
    }


    memcpy(nbVal, D->nbVal, Gp->nbVertices*sizeof(int));
    memcpy(globalMatching, D->globalMatchingP, Gp->nbVertices*sizeof(int));
    nextVar=-1;
    int d = 0;
    int sum = 0;
    for (u=0; u<Gp->nbVertices; u++){
        if ((nbVal[u]>1) &&
            ((nextVar<0) ||
             (nbVal[u]<nbVal[nextVar]) || // search variable with min domain
             ((nbVal[u] == nbVal[nextVar]) && (Gp->nbAdj[u]>Gp->nbAdj[nextVar])))) // break ties with degree
            nextVar=u;
            if(nbVal[u] == 1) d++;
            //if(nbVal[u] == 1) printf("%d=%d ",u,D->val[D->firstVal[u]]);
            sum += nbVal[u] - 1;
    }
    if (nextVar==-1){// All vertices are matched => Solution found
        nbSol++;
        if (verbose >= 1){
            printf("Solution %d: ",nbSol);
            for (u=0; u<Gp->nbVertices; u++) printf("%d=%d ",u,D->val[D->firstVal[u]]);
            printf("\n");
        }
        resetToFilter(D,Gp->nbVertices);
        return true;
    }
    
    // save the domain of nextVar to iterate on its values
    int val[D->nbVal[nextVar]];
    memcpy(val, &(D->val[D->firstVal[nextVar]]), D->nbVal[nextVar]*sizeof(int));
    
    // branch on nextVar=v, for every target node v in D(u)
    int cnts = 0;
    for(i=0; ((i<nbVal[nextVar]) && ((firstSol==0)||(nbSol==0))); i++) cnts++;

    int tmps[cnts + 1];
    memset(tmps,0,sizeof tmps);
    int idxs = 0;
    for(i=0; ((i<nbVal[nextVar]) && ((firstSol==0)||(nbSol==0))); i++) tmps[idxs++] = val[i];

    int sz = sizeof(tmps) / sizeof(tmps[0]);
    
    disorganise(tmps, idxs);
    for(i = 0;i < idxs;i++) sol[nextVar][tmps[i]]++;
    for(i=0; i < idxs;i++){
        v = tmps[i];
        if ((!removeAllValuesButOne(nextVar,v,D,Gp,Gt)) || (!matchVertex(nextVar,induced,D,Gp,Gt))){
            if (verbose == 2) printf("Inconsistency detected while matching %d to %d\n",nextVar,v);
            nbFail++;
            nbNodes++;
            resetToFilter(D,Gp->nbVertices);
        }
        else {
            if (!solves_pres(timeLimit,firstSol,induced,verbose,D,Gp,Gt,depth + 1,0)){
            // CPU time exceeded
             //resetToFilter(D,Gp->nbVertices);
             memset(D->globalMatchingT,-1,sizeof(int)*Gt->nbVertices);
             memcpy(D->nbVal, nbVal, Gp->nbVertices*sizeof(int));
             memcpy(D->globalMatchingP, globalMatching, Gp->nbVertices*sizeof(int));
             for (u=0; u<Gp->nbVertices; u++){
                D->globalMatchingT[globalMatching[u]] = u;
            }

            return false;}

            if(nbSol > 0) return true;

            
        }
        
        // restore domain sizes and global all different matching
        if(nbSol > 0) return true;
        if (verbose == 2) printf("End of branch %d=%d\n",nextVar,v);
        memset(D->globalMatchingT,-1,sizeof(int)*Gt->nbVertices);
        memcpy(D->nbVal, nbVal, Gp->nbVertices*sizeof(int));
        memcpy(D->globalMatchingP, globalMatching, Gp->nbVertices*sizeof(int));
        for (u=0; u<Gp->nbVertices; u++){
            D->globalMatchingT[globalMatching[u]] = u;
        }
    }
    return true;
}



void usage(int status){
	// print usage notice and exit with status code status
	printf("Usage:\n");
	printf("  -p FILE  Input pattern graph (mandatory)\n");
	printf("  -t FILE  Input target graph (mandatory)\n\n"); 
	printf("  -s INT   Set CPU time limit in seconds (default: 60)\n");
    printf("  -f       Stop at first solution (default: search for all solutions)\n");
	printf("  -i       Search for an induced subgraph (default: search for partial subgraph)\n");
	printf("  -v       Print solutions (default: only number of solutions)\n");
	printf("  -vv      Be verbose\n");
	printf("  -h       Print this help message\n");
	exit(status);
}

void parse(int* timeLimit, bool* firstSol, bool* i, int* verbose,  char* fileNameGp, char* fileNameGt, char* argv[], int argc){ 
	// get parameter values
	// return false if an error occurs; true otherwise
	char ch;
	extern char* optarg;
	while ( (ch = getopt(argc, argv, "lvfs:ip:t:d:h"))!=-1 ) {
		switch(ch) {
			case 'v': (*verbose)++; break;
            case 'f': *firstSol=true; break;
			case 's': *timeLimit=atoi(optarg); break;
			case 'i': *i=true; break;
			case 'p': strncpy(fileNameGp, optarg, 254); break;
			case 't': strncpy(fileNameGt, optarg, 254); break;
			case 'h': usage(0);
			default:
				printf("Unknown option: %c.\n", ch);
				usage(2);
		}
	}
	if (fileNameGp[0] == 0){
		printf("Error: no pattern graph given.\n");
		usage(2);
	}
	if (fileNameGt[0] == 0){
		printf("Error: no target graph given.\n");
		return usage(2);
	}
}

int printStats(bool timeout){
	// print statistics line and return exit status depending on timeout
	getrusage(RUSAGE_SELF, &ru);
	if (timeout)
		printf("CPU time exceeded");
	else
		printf("Run completed");
	printf(": %d solutions; %d fail nodes; %d nodes; %d.%06d seconds\n",
		   nbSol, nbFail, nbNodes,
		   (int) ru.ru_utime.tv_sec, (int) ru.ru_utime.tv_usec);
	return timeout;
}

int G[2010][2010];
int vis[2010];
int cnt[2010];

int ans = 0;
int ans1 = 0;

int max(int a, int b){
	if(a >= b) return a;
	return b;
}

bool dfs_clique(int type, int cur, int num, Tgraph* Gp, Tgraph* Gt) {
	getrusage(RUSAGE_SELF, &ru);
   	 if (ru.ru_utime.tv_sec >= 60) return true;
	int n = Gp -> nbVertices;
	if(type) n = Gt -> nbVertices;
	if(type && ans >= ans1) return 1;
	for (int i = cur + 1; i <= n; i++) {
		if (cnt[i] + num <= ans)
			return 0;
		if (G[cur][i])
		{
			int ok = 1;
			for (int j = 0; j < num; j++)
				if (!G[i][vis[j]])
				{
					ok = 0;
					break;
				}
			if (ok) {
				vis[num] = i;
				if (dfs_clique(type, i, num + 1, Gp, Gt))
					return 1;
			}
		}
	}
	ans = max(ans, num);
	return (ans == max(num, ans) ? 0 : 1);
}

bool check_clique(int type, Tgraph* Gp, Tgraph* Gt){
	getrusage(RUSAGE_SELF, &ru);
    if (ru.ru_utime.tv_sec >= 60) return true;

	int n = Gp -> nbVertices;
	if(type) n = Gt -> nbVertices;

	for (int i = n; i > 0; i--)
	{
		vis[0] = i;
		dfs_clique(type, i, 1, Gp, Gt);
		cnt[i] = ans;
	}

}

int main(int argc, char* argv[]){
	// Parameters
	char fileNameGp[1024]; 
	char fileNameGt[1024];
	int timeLimit=60;   
	int verbose = 0;       
	bool induced = false; 
    bool firstSol = false; 
	fileNameGp[0] = 0; 
	fileNameGt[0] = 0;
	parse(&timeLimit, &firstSol, &induced, &verbose, fileNameGp, fileNameGt, argv, argc);
	if (verbose >= 2)
		printf("Parameters: induced=%d firstSol=%d timeLimit=%d verbose=%d fileNameGp=%s fileNameGt=%s\n",
			   induced,firstSol,timeLimit,verbose,fileNameGp,fileNameGt);
	
	// Initialize graphs
    int nbIsolatedP, nbIsolatedT;
	Tgraph *Gp = createGraph(fileNameGp,true,&nbIsolatedP);       // Pattern graph
	Tgraph *Gt = createGraph(fileNameGt,false,&nbIsolatedT);       // Target graph
	if (verbose >= 2){
		printf("Pattern graph:\n");
		printGraph(Gp);
		printf("Target graph:\n");
		printGraph(Gt);
	}
    if ((Gp->nbVertices+nbIsolatedP > Gt->nbVertices) || (Gp->maxDegree > Gt->maxDegree))
        return printStats(false);

	// Initialize domains
	Tdomain *D = createDomains(Gp, Gt);
	if (!initDomains(induced, D, Gp, Gt)) return printStats(false);
	if (verbose >= 2) printDomains(D, Gp->nbVertices);
    
    // Check the global all different constraint
    if (!updateMatching(Gp->nbVertices,Gt->nbVertices,D->nbVal,D->firstVal,D->val,D->globalMatchingP) ||
        !ensureGACallDiff(induced,Gp,Gt,D)){
        nbFail++;
        return printStats(false);
    }

    // Math all vertices with singleton domains
    int u;
    int nbToMatch = 0;
    int toMatch[Gp->nbVertices];
    for (u=0; u<Gp->nbVertices; u++){
        D->globalMatchingT[D->globalMatchingP[u]] = u;
        if (D->nbVal[u] == 1)
            toMatch[nbToMatch++] = u;
    }
    if (!matchVertices(nbToMatch,toMatch,induced,D,Gp,Gt)){
        nbFail++;
        return printStats(false);
    }
	int avd = 0;
	for(u = 0;u < Gt->nbVertices;u++){
        Sum[u] = 0;
        for(int d = 0; d < Gt->nbAdj[u];d++){
            Sum[u] += Gt->nbAdj[Gt->adj[u][d]];
        }
        if(Gt->nbAdj[u] >= 20) avd++;
    }
    if(avd >= Gt->nbVertices / 2) dense = true;

	// Solve
   
	Tdomain *tmp_D = D;
    if(solves_pre(10,firstSol, induced, verbose, D, Gp, Gt, 0, 0)) printStats(false);
    else{
        bool find = false;
        for(int u = 1;u <= 20;u++) {
            resetToFilter(D,Gp->nbVertices);
            if(solves_pres(10 + u,firstSol, induced, verbose, D, Gp, Gt, 0, 0)){
                printStats(false);
                find = true;
                break;
            }
        }
        if(!find){
			resetToFilter(D,Gp->nbVertices);
			if(Gp->nbVertices <= 200 && Gt ->nbVertices <= 2000) {

				for(int u = 0;u < Gp->nbVertices;u++){
					for(int k = 0; k < Gp->nbAdj[u];k++){
						int nb_u = Gp->adj[u][k];
						G[u + 1][nb_u + 1] = 1;
					}
				}



				check_clique(0, Gp, Gt);

				ans1 = ans;

				ans = 0;
				memset(cnt,0,sizeof cnt);
				memset(vis,0,sizeof vis);
				memset(G,0,sizeof G);

				for(int u = 0;u < Gt->nbVertices;u++){
					for(int k = 0; k < Gt->nbAdj[u];k++){
						int nb_u = Gt->adj[u][k];
						G[u + 1][nb_u + 1] = 1;
					}
				}

				check_clique(1, Gp, Gt);

				getrusage(RUSAGE_SELF, &ru);

				if(ans < ans1 && ru.ru_utime.tv_sec < 60) {
					printStats(false);
					return 0;
				}
				else return printStats(!solve(timeLimit, firstSol, induced, verbose, D, Gp, Gt, 0, 0));
			}

			else return printStats(!solve(timeLimit, firstSol, induced, verbose, D, Gp, Gt, 0, 0));
		} 
    }

    return 0;
       

    
}
