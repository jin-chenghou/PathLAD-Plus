typedef struct{
	bool isDirected; // false iff for each edge (i,j), there exists an edge (j,i)
    bool* isLoop; // isLoop[i] = true if there is a loop on vertex i 
	int nbVertices; // Number of vertices 
	int* nbAdj;    // nbAdj[i] = number of vertices j such that (i,j) or (j,i) is an edge 
	int* nbPred;   // nbPred[i] = number of vertices j such that (j,i) is an edge and (i,j) is not an edge
	int* nbSucc;   // nbSucc[i] = number of vertices j such that (i,j) is an edge and (j,i) is not an edge
	int** adj;     // forall j in [0..nbAdj[i]-1], adj[i][j] = jth vertex adjacent to i 
	char** edgeDirection;	// if both (i,j) and (j,i) are edges then edgeDirection[i][j] = 3
							// else if (i,j) is an edge then edgeDirection[i][j] = 1
							// else if (j,i) is an edge then edgeDirection[i][j] = 2
							// else (neither (i,j) nor (j,i) is an edge) edgeDirection[i][j] = 0
    int** edgeLabel; 
    int* vertexLabel; 
    int maxDegree; 
} Tgraph;

void removeVertex(int v, Tgraph* graph){
    for (int i=0; i<graph->nbAdj[v]; i++){
        int sv = graph->adj[v][i];
        int j=0;
        while ((j<graph->nbAdj[sv]) && (graph->adj[sv][j] != v)) j++;
        if (j<graph->nbAdj[sv]){
            graph->adj[sv][j] = graph->adj[sv][--graph->nbAdj[sv]];
            if (graph->edgeDirection[sv][v] == 1) graph->nbSucc[sv]--;
            else if (graph->edgeDirection[sv][v] == 2) graph->nbPred[sv]--;
            graph->edgeDirection[sv][v] = 0;
            graph->edgeDirection[v][sv] = 0;
        }
    }
    graph->nbAdj[v] = 0;
    graph->nbSucc[v] = 0;
    graph->nbPred[v] = 0;
}

void printGraph(Tgraph* graph){
    int i, j, k;
    if (graph->isDirected)
        printf("Directed ");
    else
        printf("Non directed ");
    printf("graph with %d vertices\n",graph->nbVertices);
    for (i=0; i<graph->nbVertices; i++){
        printf("Vertex %d has %d adjacent vertices: ",
               i,graph->nbAdj[i]);
        for (j=0; j<graph->nbAdj[i]; j++){
            k = graph->adj[i][j];
            if (graph->edgeDirection[i][k] == 1)
                printf(" %d(succ)",k);
            else if (graph->edgeDirection[i][k] == 2)
                printf(" %d(pred)",k);
            else if (graph->edgeDirection[i][k] == 3)
                printf(" %d(succ and pred)",k);
            else
                printf("error !");
            
        }
        printf("\n");
        
    }
}


Tgraph* createGraph(char* fileName, bool isPatternGraph, int* nbIsolated){
	// reads data in fileName and create the corresponding graph 
    // if isPatternGraph = true, then remove isolated vertices and set nbIsolatedVertices to the number of isolated vertices
	
	FILE* fd;
	int i, j, k;
	Tgraph* graph = (Tgraph*)malloc(sizeof(Tgraph));
	
	if ((fd=fopen(fileName, "r"))==NULL){
		printf("ERROR: Cannot open ascii input file %s\n", fileName); 
		exit(1);
	}
	if (fscanf(fd,"%d",&(graph->nbVertices)) != 1){
		printf("ERROR while reading input file %s\n", fileName); 
		exit(1);
	}
    graph->vertexLabel = (int*)calloc(graph->nbVertices,sizeof(int));
    graph->edgeLabel = (int**)calloc(graph->nbVertices,sizeof(int*));
    graph->isLoop = (bool*)calloc(graph->nbVertices,sizeof(bool));
    graph->nbAdj = (int*)calloc(graph->nbVertices,sizeof(int));
	graph->nbPred = (int*)calloc(graph->nbVertices,sizeof(int));
	graph->nbSucc = (int*)calloc(graph->nbVertices,sizeof(int));
	graph->edgeDirection = (char**)malloc(graph->nbVertices*sizeof(char*));
	graph->adj = (int**)malloc(graph->nbVertices*sizeof(int*));
    graph->maxDegree = 0;
	for (i=0; i<graph->nbVertices; i++){
        graph->isLoop[i] = false;
		graph->adj[i] = (int*)malloc(graph->nbVertices*sizeof(int));
		graph->edgeDirection[i] = (char*)calloc(graph->nbVertices,sizeof(char));
		graph->edgeLabel[i] = (int*)calloc(graph->nbVertices,sizeof(int));
	}
	for (i=0; i<graph->nbVertices; i++){
		// read degree of vertex i
		if ((fscanf(fd,"%d",&(graph->nbSucc[i])) != 1) || (graph->nbSucc[i] < 0) || (graph->nbSucc[i]>=graph->nbVertices) || (feof(fd))) {
			printf("ERROR while reading input file %s: Vertex %d has an illegal number of successors (%d should be between 0 and %d)\n", 
				   fileName, i, graph->nbSucc[i], graph->nbVertices); 
			exit(1);
		}
        if (graph->nbSucc[i] > graph->maxDegree)
            graph->maxDegree = graph->nbSucc[i];
        for (j=graph->nbSucc[i]; j>0; j--){
			// read jth successor of i
			if ((fscanf(fd,"%d",&k) != 1) || (k<0) || (k>=graph->nbVertices) || (feof(fd))){
				printf("ERROR while reading input file %s: Successor %d of vertex %d has an illegal value %d (should be between 0 and %d)\n", 
					   fileName, j, i, k, graph->nbVertices); 
				exit(1);
			}
            if (i == k){ // The edge is a loop
                graph->isLoop[i] = true;
            }
            else{
                if (graph->edgeDirection[i][k] == 1){
                    printf("ERROR while reading input file %s (the successors of node %d should be all different)\n",fileName, i);
                    exit(1);
                }
                if (graph->edgeDirection[i][k] == 2){
                    // i is a successor of k and k is a successor of i
                    graph->edgeDirection[k][i] = 3;
                    graph->edgeDirection[i][k] = 3;
                    graph->nbPred[i]--;
                    graph->nbSucc[i]--;
                    graph->nbSucc[k]--;
                }
                else{
                    graph->nbPred[k]++;
                    graph->adj[i][graph->nbAdj[i]++] = k;
                    graph->adj[k][graph->nbAdj[k]++] = i;
                    graph->edgeDirection[i][k] = 1;
                    graph->edgeDirection[k][i] = 2;
                }
            }
		}
	}
	fclose(fd);
    if (isPatternGraph){//remove isolated vertices
        int idVertex[graph->nbVertices];
        *nbIsolated = 0;
        for (i=0; i<graph->nbVertices; i++){
            if (graph->nbAdj[i] == 0){
                (*nbIsolated)++;
            }
            idVertex[i] = i-*nbIsolated;
        }
        if (*nbIsolated > 0){
            for (i=0; i<graph->nbVertices; i++){
                int ni = idVertex[i];
                if (graph->nbAdj[i]>0){
                if (ni == i){
                    for (int j=0; j<graph->nbVertices; j++){
                        int nj = idVertex[j];
                        if (graph->nbAdj[j]>0)
                            graph->edgeDirection[i][nj] = graph->edgeDirection[i][j];
                    }
                    for (int j=0; j<graph->nbAdj[i]; j++){
                        int si = graph->adj[i][j];
                        int nsi = idVertex[si];
                        graph->adj[i][j] = nsi;
                    }
                }
                else {
                    graph->isLoop[ni] = graph->isLoop[i];
                    graph->nbAdj[ni] = graph->nbAdj[i];
                    graph->nbPred[ni] = graph->nbPred[i];
                    graph->nbSucc[ni] = graph->nbSucc[i];
                    memset(graph->edgeDirection[ni],0,graph->nbVertices*sizeof(char));
                    for (int j=0; j<graph->nbAdj[i]; j++){
                        int si = graph->adj[i][j];
                        int nsi = idVertex[si];
                        graph->adj[ni][j] = nsi;
                        graph->edgeDirection[ni][nsi] = graph->edgeDirection[i][si];
                    }
                }
                }
            }
        }
        graph->nbVertices -= *nbIsolated;
    }
    // computing vertex and edge labels
    for (i=0; i<graph->nbVertices; i++){
        for (j=0; j<graph->nbAdj[i]; j++){
            int si=graph->adj[i][j];
            for (k=0; k<graph->nbAdj[si]; k++){
                int ssi = graph->adj[si][k];
                if (ssi != i){
                    if (graph->edgeDirection[i][ssi] > 0) graph->edgeLabel[i][ssi]++;
                    if (graph->edgeDirection[ssi][i] > 0) graph->vertexLabel[i]++;
                }
            }
        }
    }
	
	graph->isDirected = false;
	for (i=0; i<graph->nbVertices && !graph->isDirected; i++){
		for (j=0; j<graph->nbAdj[i] && !graph->isDirected; j++){
			graph->isDirected = (graph->edgeDirection[i][graph->adj[i][j]]==1) || (graph->edgeDirection[i][graph->adj[i][j]]==2);
		}
	}
	return graph;
}

