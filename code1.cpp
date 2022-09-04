#include <iostream>

int main()
{
	int a = 1;
	int array[40][30][20][10];

	for(int i =0; i < 40;i++){
		for(int j=0; j < 30;j++){
			for(int k=0; k < 20;k++ ){
				for(int l=0; l <10;l++){
					array[i][j][k][l]=array[i-1][j-1][k+1][l-1];
				}
			}
		}
	}

return 0;

}
