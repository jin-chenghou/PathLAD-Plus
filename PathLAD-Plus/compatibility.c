bool compatibleVertexLabels(int l1, int l2){
	// return true iff a vertex labelled with l1 may be matched with a vertex labelled with l2
	return (l1 <= l2);
}

bool compatibleEdgeLabels(int l1, int l2){
	// return true iff an edge labelled with l1 may be matched with an edge labelled with l2
	return (l1 <= l2);
}