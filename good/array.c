int pseudo_random(int a) {
	return (a * 48271) % 2147483647;
}

int swap(*int a, *int b) {
	int tmp = *a;
	*a = *b;
	*b = tmp;
	return tmp;
}

int partition(*int A, int low, int high) {
	int pivot = A[low];
	swap(&A[low], &A[high]);
	int index = low;
	int i = low;
	while (i < high) {
		if (A[i] <= pivot) {
			swap(&A[i], &A[index]);
			index = index + 1;
		};
		i = i + 1;
	};
	swap(&A[index], &A[high]);
	return index;
}

int quicksort(*int A, int low, int high) {
	if (low < high) {
		int p = partition(A, low, high);
		quicksort(A, low, p - 1);
		quicksort(A, p + 1, high);
	};
	return low;
}

int print_array(*int A, int size) {
	int i = 0;
	while (i < size) {
		print A[i];
		print " ";
		i = i + 1;
	};
	return i;
}

int main () {
	int size = 42;
	*int p = new int[size] filled with 500;

	{
		int seed = 13;
		int i = 0;
		while (i < size) {
			seed = pseudo_random(seed);
			p[i] = seed % 1000;
			i = i + 1;
		};
	};

	print_array(p, size);
	print "\n";

	quicksort(p, 0, size - 1);

	print_array(p, size);
	print "\n";

	return 0;
}
