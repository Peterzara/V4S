function main() {
	var sum = 0;
	var i = 5;
	while(i >= 1){
		invariant(sum + i*(i + 1)/2 == 15);
		invariant(i >= 0);
		sum = sum + i;
		i = i - 1;
	}
	assert(sum == 15);
}
