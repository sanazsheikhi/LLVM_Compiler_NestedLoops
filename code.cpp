#include <iostream>

int main()
{
	int a = 0;
	int A[40][30][20][10];
	int B[40][30][20][10];

	for(int i =0; i < 40;i++){
		a+=10;
		for(int j=0; j < 30;j++){
			for(int k=0; k < 20;k++ ){
				for(int l=0; l <10;l++){
					A[i][j][k][l]=A[i-1][j-1][k-1][l-1];
					B[i][j][k][l]=B[i-1][j-1][k+1][l+1];
				}
				a+=5;
			}
		}
	}

return 0;

}
