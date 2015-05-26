int replace(**int x) {
	**x = **x;
	return 0;
}

int main () {
	int i = 0;
	*int p = &i;
	*p = 500;
	**int pp = &p;

	replace(pp);

	return i;
}
