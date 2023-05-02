#define white 0
#define grey 1
#define black 2
#define toBeDeleted 3
#define deleted 4

void addToDelete(int u, int* list, int* nb, int* marked){
	if (marked[u]<toBeDeleted){
		list[(*nb)++]=u;
		marked[u]=toBeDeleted; 
	}
}

bool updateMatching(int sizeOfU, int sizeOfV, int* degree, int* firstAdj, int*  adj, int* matchedWithU){
	// input:
	// sizeOfU = number of vertices in U
	// sizeOfV = number of vertices in V
	// degree[u] = number of vertices of V which are adjacent to u
	// firstAdj[u] = pos in adj of the first vertex of V adjacent to u
	// adj[firstAdj[u]..firstAdj[u]+sizeOfU[u]-1] = vertices of V adjacent to u
	
	// input/output:
	// matchedWithU[u] = vertex of V matched with u
	
	// returns true if there exists a matching that covers U, i.e., if for every u in 0..nbU-1, 
	// there exists a different v in 0..nb-1 such that v is adjacent to u;
	// returns false otherwise
	
	if (sizeOfU>sizeOfV) return false; // trivial case of infeasibility
	
	int matchedWithV[sizeOfV]; // matchedWithV[matchedWithU[u]]=u
	int nbPred[sizeOfV]; // nbPred[i] = nb of predecessors of the ith vertex of V in the DAG
	int pred[sizeOfV][sizeOfU]; // pred[i][j] = jth predecessor the ith vertex of V in the DAG
	int nbSucc[sizeOfU]; // nbSucc[i] = nb of successors of the ith vertex of U in the DAG
	int succ[sizeOfU][sizeOfV]; // succ[i][j] = jth successor of the ith vertex of U in the DAG
	int listV[sizeOfV], listU[sizeOfU], listDV[sizeOfV], listDU[sizeOfU];
	int nbV, nbU, nbDV, nbDU;
	int i,j,k,stop,u,v;
	int markedV[sizeOfV], markedU[sizeOfU];
	// markedX[i]=white if X[i] is not in the DAG
	// markedX[i]=grey if X[i] has been added to the DAG, but not its successors
	// markedX[i]=black if X[i] and its successors have been added to the DAG
	// markedX[i]=toBeDeleted if X[i] must be deleted from the DAG
	// markedX[i]=deleted if X[i] has been deleted from the DAG
	int nbUnmatched = 0; // number of vertices of U that are not matched 
	int unmatched[sizeOfU]; // vertices of U that are not matched
	int posInUnmatched[sizeOfU]; // unmatched[posInUnmatched[u]]=u
	
	// initialize matchedWithV and unmatched
	memset(matchedWithV,-1,sizeOfV*sizeof(int));
	for (u=0; u<sizeOfU; u++)
		if (matchedWithU[u] >= 0) 
			matchedWithV[matchedWithU[u]]=u;
		else{
			posInUnmatched[u]=nbUnmatched;
			unmatched[nbUnmatched++]=u;
		}
	// try to match unmatched vertices of U with free vertices of V
	j=0;
	while (j<nbUnmatched){
		u = unmatched[j];
		for (i=firstAdj[u]; ((i<firstAdj[u]+degree[u]) && (matchedWithV[adj[i]] >= 0)); i++);
		if (i==firstAdj[u]+degree[u]) j++; // no free vertex for u
		else{
			v=adj[i]; // v is free => match u with v
			matchedWithU[u]=v; 
			matchedWithV[v]=u; 
			unmatched[j]=unmatched[--nbUnmatched];
			posInUnmatched[unmatched[j]]=j;
		}
	}
	
	while (nbUnmatched > 0){ // Try to increase the number of matched vertices
		// step 1 : build the DAG
		memset(markedU,white,sizeOfU*sizeof(int));
		memset(nbSucc,0,sizeOfU*sizeof(int));
		memset(markedV,white,sizeOfV*sizeof(int));
		memset(nbPred,0,sizeOfV*sizeof(int));
		//first layer of the DAG from the free nodes of U
		nbV=0;
		for (j=0; j<nbUnmatched; j++){
			u=unmatched[j]; // u is a free node of U
			markedU[u]=black;
			for (i=firstAdj[u]; i<firstAdj[u]+degree[u]; i++){
				v=adj[i]; // add edge (u,v) to the DAG
				pred[v][nbPred[v]++]=u;
				succ[u][nbSucc[u]++]=v;
				if (markedV[v]==white){// first time v is added to the DAG
					markedV[v]=grey; 
					listV[nbV++]=v;
				}
			} 
		}
		stop=0;
		while ((stop==0) && (nbV>0)){
			// build next layer from nodes of V to nodes of U
			nbU=0;
			for (i=0; i<nbV; i++){
				v=listV[i];
				markedV[v]=black;
				u=matchedWithV[v]; 
				if (markedU[u]==white){// edge (v,u) belongs to the DAG
					markedU[u]=grey; 
					listU[nbU++]=u;
				}
			}
			// build next layer from nodes of U to nodes of V
			nbV=0;
			for (j=0; j<nbU; j++){
				u=listU[j];
				markedU[u]=black;
				for (i=firstAdj[u];i<firstAdj[u]+degree[u];i++){
					v=adj[i]; 
					if (markedV[v]!=black){// add edge (u,v) to the DAG
						pred[v][nbPred[v]++]=u;
						succ[u][nbSucc[u]++]=v;
						if (markedV[v]==white){// first time v is added to the DAG
							markedV[v]=grey; 
							listV[nbV++]=v;
						}
						if (matchedWithV[v]==-1) // we have found a free node !
							stop=1; 
					}
				}
			}
		}
		if (nbV==0) return false;
		
		// step 2: look for augmenting paths
		for (k=0; k<nbV; k++){ 
			v=listV[k];
			if ((matchedWithV[v]==-1) && (nbPred[v]>0)){// v is the final node of an augmenting path
				int path[sizeOfU+sizeOfV];
				int length = 1;
				path[0]=v;
				nbDV=0; 
				nbDU=0;
				addToDelete(v,listDV,&nbDV,markedV);
				do{
					u=pred[v][0]; // (u,v) belongs to the augmenting path
					path[length++]=u;
					addToDelete(u,listDU,&nbDU,markedU);
					if (matchedWithU[u]!=-1){// u is not the initial node of the augmenting path
						v=matchedWithU[u]; // (v,u) belongs to the augmenting path
						path[length++]=v;
						addToDelete(v,listDV,&nbDV,markedV);
					}
				} while (matchedWithU[u]!=-1);
				
				// delete nodes of listDV and listDU
				while ((nbDV>0) || (nbDU>0)){
					while (nbDV>0){ // delete v
						v=listDV[--nbDV]; markedV[v]=deleted;
						u=matchedWithV[v];
						if (u!=-1) addToDelete(u,listDU,&nbDU,markedU);
						for (i=0; i<nbPred[v]; i++){
							u=pred[v][i]; // delete edge (u,v)
							for (j=0; ((j<nbSucc[u]) && (v!=succ[u][j])); j++);
							succ[u][j]=succ[u][--nbSucc[u]];
							if (nbSucc[u]==0) addToDelete(u,listDU,&nbDU,markedU);
						}
					}
					while (nbDU>0){// delete u
						u = listDU[--nbDU]; markedU[u]=deleted;
						v=matchedWithU[u];
						if (v!=-1) addToDelete(v,listDV,&nbDV,markedV);
						for (i=0; i<nbSucc[u]; i++){// delete edge (u,v)
							v=succ[u][i];
							for (j=0; ((j<nbPred[v]) && (u!=pred[v][j])); j++);
							pred[v][j]=pred[v][--nbPred[v]];
							if (nbPred[v]==0) addToDelete(v,listDV,&nbDV,markedV);
						}
					}
				}
				// Remove the last node of the augmenting path from the set of unmatched vertices
				u=path[length-1]; 
				i=posInUnmatched[u];
				unmatched[i]=unmatched[--nbUnmatched];
				posInUnmatched[unmatched[i]]=i;
				// Update the matching wrt the augmenting path
				while (length>1){
					u=path[length-1]; v=path[length-2]; length-=2;
					matchedWithU[u]=v;
					matchedWithV[v]=u;
				}
			}
		}
	}
	return true;
}

void DFS(int nbU, int nbV, int u, bool* marked, int* nbSucc, int succ[nbV][nbU], int* matchedWithU, int* order, int* nb){
	// perform a depth first search, starting from u, in the bipartite graph Go=(U,V,E) such that
	// U = vertices of Gp
	// V = vertices of Gt
	// E = { (u,matchedWithU[u]) / u is a vertex of Gp } U
	//     { (v,u) / v is a vertex of D[u] which is not matched to v}
	// Given a vertex v of Gt, nbSucc[v]=number of successors of v and succ[v]=list of successors of v
	// order[nb^out+1..nb^in] contains the vertices discovered by the DFS
	int i;
	marked[u]=true;
	int v=matchedWithU[u]; // the only one predecessor of v is u
	for (i=0; i<nbSucc[v]; i++)
		if (!marked[succ[v][i]]) 
			DFS(nbU,nbV,succ[v][i],marked,nbSucc,succ,matchedWithU,order,nb);
	// we have finished with u => number it
	order[*nb]=u; (*nb)--;
}

void SCC(int nbU, int nbV, int* numV, int* numU, 
		 int* nbSucc, int succ[nbV][nbU], 
		 int* nbPred, int pred[nbU][nbV], int* matchedWithU,int* matchedWithV){
	// postrelation: numV[v]==numU[u] iff they belong to the same
	// strongly connected component in the bipartite graph Go=(U,V,E) such that
	// U = vertices of Gp
	// V = vertices of Gt
	// E = { (u,matchedWithU[u]) / u is a vertex of Gp } U
	//     { (v,u) / v is a vertex of D[u] which is not matched to v}
	// Given a vertex v of Gt, nbSucc[v]=number of sucessors of v and succ[v]=list of successors of v
	int order[nbU];
	bool marked[nbU];
	int fifo[nbV];
	int u, v, i, j, k, nbSCC, nb;
	
	// Order vertices of Gp wrt DFS
	memset(marked,false,nbU*sizeof(bool));
	nb=nbU-1;
	for (u=0; u<nbU; u++)
		if (!marked[u]) DFS(nbU,nbV,u,marked,nbSucc,succ,matchedWithU,order,&nb);
	
	// traversal starting from order[0], then order[1], ...
	nbSCC=0;
	memset(numU,-1,nbU*sizeof(int));
	memset(numV,-1,nbV*sizeof(int));
	for (i=0; i<nbU; i++){
		u=order[i];
		v=matchedWithU[u];
		if (numV[v]==-1){ // v belongs to a new SCC
			nbSCC++;
			k=1; fifo[0]=v;
			numV[v]=nbSCC;
			while (k>0){
				v=fifo[--k];
				u=matchedWithV[v];
				if (u!=-1){
					numU[u]=nbSCC;
					for (j=0; j<nbPred[u]; j++){
						v=pred[u][j];
						if (numV[v]==-1){
							numV[v]=nbSCC;
							fifo[k++]=v;
						}
					}
				}
			}
		}
	}
}


bool ensureGACallDiff(bool induced, Tgraph* Gp, Tgraph* Gt, Tdomain* D){
	// precondition: D->globalMatchingP is an all different matching of the pattern vertices
	// postcondition: filter domains wrt GAC(allDiff)
	//                return false if an inconsistency is detected; true otherwise
	
	// Build the bipartite directed graph Go=(U,V,E) such that
	// E = { (u,v) / u is a vertex of Gp which is matched to v (i.e., v=D->globalMatchingP[u])} U
	//     { (v,u) / v is a vertex of Gt which is in D(u) but is not matched to u}
	int nbPred[Gp->nbVertices]; // nbPred[u] = nb of predecessors of u in Go
	int pred[Gp->nbVertices][Gt->nbVertices]; // pred[u][i] = ith predecessor of u in Go
	int nbSucc[Gt->nbVertices]; // nbSucc[v] = nb of successors of v in Go
	int succ[Gt->nbVertices][Gp->nbVertices]; // succ[v][i] = ith successor of v in Go
	int u,v,i,w,oldNbVal,nbToMatch;
	int numV[Gt->nbVertices], numU[Gp->nbVertices], toMatch[Gp->nbVertices];
	bool used[Gp->nbVertices][Gt->nbVertices];
	memset(numV,false,Gt->nbVertices*sizeof(int));
	memset(nbSucc,0,Gt->nbVertices*sizeof(int));
	memset(nbPred,0,Gp->nbVertices*sizeof(int));
	memset(numU,false,Gp->nbVertices*sizeof(int));
	for (u=0; u<Gp->nbVertices; u++){
		for (i=0; i<D->nbVal[u]; i++){
			v=D->val[D->firstVal[u]+i]; // v in D(u)
			used[u][v]=false;
			if (v != D->globalMatchingP[u]){
				pred[u][nbPred[u]++]=v; 
				succ[v][nbSucc[v]++]=u; 
			}
		}
	}
	
	// mark as used all edges of paths starting from free vertices
	int list[Gt->nbVertices];
	int nb=0;
	for (v=0; v<Gt->nbVertices; v++){
		if (D->globalMatchingT[v] < 0){ // v is free
			list[nb++]=v;
			numV[v]=true;
		}
	}
	while (nb>0){
		v=list[--nb];
		for (i=0; i<nbSucc[v]; i++){
			u=succ[v][i];
			used[u][v]=true;
			if (numU[u]==false){
				numU[u]=true;
				w=D->globalMatchingP[u];
				used[u][w]=true;
				if (numV[w]==false){
					list[nb++]=w;
					numV[w]=true;
				}
			}
		}
	}
	
	// look for strongly connected components in Go
	SCC(Gp->nbVertices,Gt->nbVertices,numV,numU,nbSucc,succ,nbPred,pred,D->globalMatchingP,D->globalMatchingT);
	
	// remove v from D[u] if (u,v) is not marked as used 
	//                    and u and v are not in the same SCC 
	//                    and D->globalMatchingP[u] != v
	nbToMatch = 0;
	for (u=0; u<Gp->nbVertices; u++){
		oldNbVal = D->nbVal[u];
		for (i=0; i<D->nbVal[u]; i++){
			v=D->val[D->firstVal[u]+i]; // v in D(u)
			if ((!used[u][v]) && (numV[v]!=numU[u]) && (D->globalMatchingP[u]!=v))
				if (!removeValue(u,v,D,Gp,Gt)) return false;
		}
		if (D->nbVal[u] == 0) return false;
		if ((oldNbVal>1) && (D->nbVal[u]==1)) toMatch[nbToMatch++] = u;
	}
	return matchVertices(nbToMatch,toMatch,induced,D,Gp,Gt);
}
