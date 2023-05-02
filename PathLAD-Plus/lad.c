bool checkLAD(bool induced, int u, int v, Tdomain* D, Tgraph* Gp, Tgraph* Gt){
	// return true if G_(u,v) has a adj(u)-covering matching; false otherwise
	int u2, v2, i, j;
	int nbMatched = 0;
	
	// special case when u has only 1 adjacent node => no need to call Hopcroft and Karp
	if (Gp->nbAdj[u]==1){
		u2 = Gp->adj[u][0]; // u2 is the only node adjacent to u
		v2 = D->matching[D->firstMatch[u][v]];
		if ((v2 != -1) && (isInD(u2,v2,D))) return true;
		// look for a support of edge (u,u2) for v
		for (i=D->firstVal[u2]; i<D->firstVal[u2]+D->nbVal[u2]; i++){
		  if ((compatibleEdgeLabels(Gp->edgeLabel[u][u2], Gt->edgeLabel[v][D->val[i]]))
			  && (isCompatible(induced, Gp->edgeDirection[u][u2], Gt->edgeDirection[v][D->val[i]]))){
				D->matching[D->firstMatch[u][v]] = D->val[i];
				return true;
			}
		}
	
		return false;
	}
	
	// general case (when u has more than 1 adjacent node)
	for (i=0; i<Gp->nbAdj[u]; i++){ 
		// remove from the matching of G_(u,v) edges which no longer belong to G_(u,v)
		u2 = Gp->adj[u][i];
		v2 = D->matching[D->firstMatch[u][v]+i];
		if ((v2 != -1) && (isInD(u2,v2,D))) nbMatched++;
	}
	if (nbMatched == Gp->nbAdj[u]) return true; // The matching still covers adj(u)
	
	
	// Build the bipartite graph
	// let U be the set of nodes adjacent to u
	// let V be the set of nodes that are adjacent to v, and that belong to domains of nodes of U
	int num[Gt->nbVertices], numInv[Gt->nbVertices];
	int nbComp[Gp->nbAdj[u]]; // nbComp[u]=number of elements of V that are compatible with u
	int firstComp[Gp->nbAdj[u]]; 
	int comp[Gp->nbAdj[u]*Gt->nbVertices]; // comp[firstComp[u]..firstComp[u]+nbComp[u]-1] = nodes of Gt that are compatible with u
	int nbNum=0;
	int posInComp=0;
	int matchedWithU[Gp->nbAdj[u]];
	memset(num,-1,Gt->nbVertices*sizeof(int));
	for (i=0; i<Gp->nbAdj[u]; i++){
		u2 = Gp->adj[u][i]; // u2 is adjacent to u
		// search for all nodes v2 in D[u2] which are adjacent to v
		nbComp[i]=0;
		firstComp[i]=posInComp;
		if (D->nbVal[u2]>Gt->nbAdj[v]){
			for (j=D->firstVal[u2]; j<D->firstVal[u2]+D->nbVal[u2]; j++){
				v2 = D->val[j]; // v2 belongs to D[u2]
				if ((compatibleEdgeLabels(Gp->edgeLabel[u][u2], Gt->edgeLabel[v][v2])) &&
					(isCompatible(induced, Gp->edgeDirection[u][u2], Gt->edgeDirection[v][v2]))){ 
					// v2 is a successor of v and the label of (u,u2) is equal to the label of (v,v2)  
					if (num[v2]<0){ // v2 has not yet been added to V
						num[v2]=nbNum;
						numInv[nbNum++]=v2;
					} 
					comp[posInComp++]=num[v2];
					nbComp[i]++;
				}
			}
		}
		else{
			for (j=0; j<Gt->nbAdj[v]; j++){
				v2 = Gt->adj[v][j]; // v2 is a successor of v
				if ((isInD(u2,v2,D)) && (compatibleEdgeLabels(Gp->edgeLabel[u][u2], Gt->edgeLabel[v][v2])) &&
					(isCompatible(induced, Gp->edgeDirection[u][u2], Gt->edgeDirection[v][v2]))){ 
					// v2 belongs to D[u2]  and the label of (u,u2) is equal to the label of (v,v2)
					if (num[v2]<0){ // v2 has not yet been added to V
						num[v2]=nbNum;
						numInv[nbNum++]=v2;
					} 
					comp[posInComp++]=num[v2];
					nbComp[i]++;
				}
			}			
		}
		if (nbComp[i]==0) return false; // u2 has no compatible vertex in adj[v]
		v2 = D->matching[D->firstMatch[u][v]+i]; // u2 is matched to v2 in the matching that supports (u,v)
		if ((v2 != -1) && (isInD(u2,v2,D))) matchedWithU[i]=num[v2];
		else matchedWithU[i]=-1;
	}
	// Call Hopcroft Karp to update the matching
	if (!updateMatching(Gp->nbAdj[u],nbNum,nbComp,firstComp,comp,matchedWithU)) return false;
	for (i=0; i<Gp->nbAdj[u]; i++) D->matching[D->firstMatch[u][v]+i] = numInv[matchedWithU[i]];
	return true;
}

