function main(i) {
	var sum = 0;
	assume(i >= 1);
	while(i >= 1){
		invariant(sum >= 0);
		var j = 1;
		while(i >= j){
			invariant(sum >= 0);
			invariant(j >= 0);
			sum = sum + j;
			j = j + 1;
		}
		i = i - 1;
	}
	assert(sum >= 0)
}
