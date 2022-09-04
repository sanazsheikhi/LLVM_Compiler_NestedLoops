#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Instructions.h"
#include <sstream>
#include <list>
#include <set>
#include <unordered_map>
//#include "llvm/IR/Value.h"

using namespace llvm;
using namespace std;
namespace {
        class SkeletonPass;
	int block_sizes[1000];
	int operands[2000][10];
	const char* opcode[2000];
	int instruction_changes[500][10];
	Value* value_star_map[2000][10];
	int opcode_index = 0;
	int index_changes = 0;

	class LoopManager{

	int nodes;
	list<int> *Graph;
	list<int> *VV;
	int *visited_nodes;
	set<int> set,tmp_set;
	list<int>  *blocks;
	int count_instruction;
	int loops_sizes[1000];	
	int loop_block_instruction_size[1000];	
		
	public:
	LoopManager(int node_count, list<int>  *blocks){//, int *block_sizes){
		nodes = node_count;
		Graph = new list<int>[nodes]; // allocate space for graph
		VV  = new list<int>[nodes];
		visited_nodes = new int[nodes];
		for(int i=0; i < nodes; i++)		
			visited_nodes[i] = 0;
		this->blocks = blocks;
/*		errs() << "check"<<"\n";
		for(int i =0; i< nodes;i++)
			errs()<<i<<" " <<block_sizes[i]<<"\n";*/
	}
	int loop_detector(int node, int parent=-100){
		//DFS
		int extra = 0;
		int instructions = 0;
		if(node != 0){
//			errs()<<node<<"--> ";
//			tmp_set.insert(node);
			instructions += block_sizes[node];
		}
		visited_nodes[node] = 1;
		list<int>::iterator it;
		for(it = Graph[node].begin(); it != Graph[node].end();it++){
			if(visited_nodes[*it] == 0) {
					
					tmp_set.insert(node);
					if(loop_detector(*it,node) == 1) {		
					instructions += block_sizes[*it];
					return 1;
				}
				else{
					extra++; 
				}
			}
			else if (*it != parent && parent != -100){
                                tmp_set.insert(node);
                                tmp_set.insert(*it);
                                set.insert(*it);
//				errs()<<*it<<"\n";
				instructions += block_sizes[*it];
//				errs()<<"size "<<(tmp_set.size()- extra);
				loops_sizes[*it] = tmp_set.size() - extra;		
				loop_block_instruction_size[*it] = instructions;

				std::set<int>::iterator it_vv;
				for(it_vv= tmp_set.begin();it_vv != tmp_set.end();it_vv++)
				{
					VV[*it].push_back(*it_vv);
				}
				tmp_set.clear();
				return 1;
			}
		}
		return 0;
	}
	int DFS(){
		for(int i=0; i < nodes; i++)		
			visited_nodes[i] = 0;

		for(int i=0; i < nodes; i++){
			if(visited_nodes[i] == 0){
				loop_detector(i, -100);
				errs()<<"\n";
			}
		}
		return 0;		
	}
	int nested_loop_detector(int inner, int outer) {
		// Using BFS algorithm to find reachability of outer loop from inner loop
		// To verify nested loop.
	
		int *visited_nodes_1 = new int[nodes]; 
		for (int i = 0; i < nodes; i++) 
	        	visited_nodes_1[i] = 0; 
		list<int> queue; 
		visited_nodes_1[inner] = 1; 
	        queue.push_back(inner); 
		list<int>::iterator it;
		while (!queue.empty()) 
    		{
			 inner = queue.front(); 
		         queue.pop_front(); 
			 for (it = Graph[inner].begin(); it != Graph[inner].end(); ++it) { 
				 if (*it == outer) 
			                return 1;
				if (!visited_nodes_1[*it]) { 
			                visited_nodes_1[*it] = 1; 
			                queue.push_back(*it); 

           			 } 
			}
		}
		  return 0;
	}

        bool perfect_loop_detector(int outer, int inner){
                int index, size;
                list<int> tmp;
                list<int>::iterator it,it1;

                it = VV[outer].begin();
                if(it == VV[outer].end())
                        return false;

                if( *it == 0)
                        it++;

                if(it == VV[outer].end())
                        return false;
                else
                        it++;

                if(it == VV[outer].end())
                        return false;
                else
                        index = *(it);
                size = block_sizes[index];
                if(size > 2){
                        return false;
                }

                it1 = VV[outer].begin();
                while(it1 != VV[outer].end() && *it1 != inner){
                        it1++;
                }
                if(it1 == VV[outer].end())
                        false;
                else
                        it1++;

                if(it1 == VV[outer].end())
                        false;
                else
                        index = *it1;

                size = block_sizes[index];
                if(size > 1){
                        return false;
                }
                return true;
        }

bool dependency_check(int outer, int inner){
		
		int index_outer = -1;
		int index_inner = -1;
		int loop_stride1 = -1;
		int loop_stride2 = -1;
		int lhs_const_outer = -1;
		int rhs_const_outer = -1;
		int lhs_const_inner = -1;
		int rhs_const_inner = -1;

		int array1 = -1;
		int array2 = -1;
		int lhs_tmp = -1;
		int rhs_tmp = -1;
		int tmp = -1;
		int store_index = 0;
		int getelemptr_index = 0;
		bool flag = true;
//////////////////////////////////////////////////////////////////////////////
		// prind the operand matrix
		/*for(int i=0; i < opcode_index; i++){
			errs()<< opcode[i]<<" : ";
			for(int j = 0; j < 10;j++)
				errs()<<" "<<operands[i][j];
			errs()<<"\n";
		}*/

/////////////////////////////////////////////////////////////////////////////
		// finiding indices of the loops (register) using load command
		for(int i=0; i < opcode_index; i++){
			if(operands[i][0] == outer && operands[i][1] == 1)
			{
				index_outer = operands[i][3];
				break;
			}
		}
		
		for(int j=0; j < opcode_index; j++){
			if(operands[j][0] == inner && operands[j][1] == 1)
			{
				index_inner = operands[j][3];
				break;
			}
		}
		while(flag && store_index < opcode_index){
		// Following up indices in store and getelementptr instructions
		for(int i = store_index; i < opcode_index; i++){
			if(operands[i][1] == 2 && operands[i-1][1] == 10){ // finding store command after getelementptr command	
				store_index = i;
				lhs_tmp = operands[i][4];
				rhs_tmp = operands[i][3];
				break;
			}
		}
		
		int cc = 0; // to consider the last 3 getelementptr
		lhs_const_outer = 0;
		lhs_const_inner = 0;
		tmp = lhs_tmp;
		for(int i= store_index-1; i >= 0 ; i--){ // reaching to getelement bottom-up
			if(operands[i][2] == tmp && operands[i][1] == 10){
				cc++;
				getelemptr_index = i;
				tmp = operands[i][3];
		
				if(operands[i-2][1] == 5){
					if( lhs_const_outer  == 0 && operands[i-3][3] == index_outer){
						lhs_const_outer = operands[i-2][4];
						}
					else if( lhs_const_inner  == 0 && operands[i-3][3] == index_inner){
						lhs_const_inner = operands[i-2][4];
						}
					}
				else if(operands[i-2][1] == 6){
//					errs()<<"lhs5555"<<" index_outer "<<index_outer<<" index_inner "<<index_inner<<" operands[i-2][3] "<< operands[i-2][3]<< "\n";
					if(lhs_const_outer  == 0 && operands[i-3][3] == index_outer){
						lhs_const_outer = -1 * operands[i-2][4];
						}
					else if(lhs_const_inner  == 0 && operands[i-3][3] == index_inner){
						lhs_const_inner = -1 * operands[i-2][4];
						}
					}
			if(cc == 3){ 
				break;
			}
		}
	}

		for(int i = getelemptr_index -1; i >= 0; i--){
			if(operands[i][1] == 1 && operands[i][2] == rhs_tmp){
				tmp = operands[i][3];
				getelemptr_index = i-1;	
				break;
			}
		}

		rhs_const_outer = 0;
		rhs_const_inner = 0;
		cc =0;
		for(int i= getelemptr_index; i >= 0 ; i--){ // reaching to getelement bottom-up
			if(operands[i][2] == tmp && operands[i][1] == 10){
				cc++;
				getelemptr_index = i;
				tmp = operands[i][3];
		
				if(operands[i-2][1] == 5){
					if( rhs_const_outer  == 0 && operands[i-3][3] == index_outer)
						rhs_const_outer = operands[i-2][4];
					else if(  rhs_const_inner  == 0 && operands[i-3][3] == index_inner)
						rhs_const_inner = operands[i-2][4];
					}

				else if(operands[i-2][1] == 6){
					if(rhs_const_outer  == 0 && operands[i-3][3] == index_outer)
						rhs_const_outer = -1 * operands[i-2][4];
					else if(rhs_const_inner  == 0 && operands[i-3][3] == index_inner)
						rhs_const_inner = -1 * operands[i-2][4];
					}
			if(cc == 3){
				break;
			}
		}	
	}	

//		 errs()<<"rhs_const_outer: "<<rhs_const_outer<<" rhs_const_inner: "<<rhs_const_inner<<" lhs_const_outer: "<<lhs_const_outer<<" lhs_const_inner: "<<lhs_const_inner<<" array1: "<<array1<<" array2: "<<array2<<"\n";
		
		 int distance_outer = 0;
		 int distance_inner = 0;
		 distance_outer = rhs_const_outer - lhs_const_outer;
		 distance_inner = rhs_const_inner - lhs_const_inner;
		 if(distance_outer < 0 && distance_inner > 0){
//			 errs()<<"Loops are Dependent and Cann't be rearranged\n\n";
			flag = false;			 
		 }
		
		store_index++; // to go to next store command in block for next array.
		}//end while
	
		if(flag){
		errs()<<"Loops are Not Dependent and Can be interchanged\n\n";
		
		// We store the block numbers, the instruction and operands that should be exchanged.

		instruction_changes[index_changes][0] = inner; // block number to use for swap
		instruction_changes[index_changes][1] = outer; // block number to use for swap
		instruction_changes[index_changes][2] = 3; // instruction (icmp = 3)
		instruction_changes[index_changes][3] = 1;  // operand (the second operand of icmp , the constant number)

		index_changes++;
		
		instruction_changes[index_changes][0] = operands[store_index][0]; //block number to be changed
		instruction_changes[index_changes][1] = operands[store_index][0]; //block number to be changed
		instruction_changes[index_changes][2] = 1; // instruction (load = 1)
		instruction_changes[index_changes][3] = 0; // operand (the first operand of load)
		instruction_changes[index_changes][4] = index_inner; // operand (the first operand of load)
		instruction_changes[index_changes][5] = index_outer; // operand (the first operand of load)

		index_changes++;

		instruction_changes[index_changes][0] = operands[store_index][0]+1; //block after the body of inner loop (inner loop jump)
		instruction_changes[index_changes][1] = operands[store_index][0]+2; //block after the body of inner loop (outer loop jump)
		instruction_changes[index_changes][2] = 1; // instruction (load = 1)
		instruction_changes[index_changes][3] = 0; // operand (the first operand of load)
		instruction_changes[index_changes][4] = index_inner; // operand (the first operand of load)
		instruction_changes[index_changes][5] = index_outer; // operand (the first operand of load)

		index_changes++;
	     }
	     else{
		 errs()<<"Loops are Dependent and Can Not be interchanged\n\n";
		}
	     
	return true;	
		
	}


	void add_edge(int parent, int child){
		Graph[parent].push_back(child);
	
	}

        void print_loops(){
                list<int>::iterator it,it1;
                for(int i=0; i<nodes;i++){
                        for(it=VV[i].begin(); it != VV[i].end(); it++){
                                errs()<<*it<<" --> ";
                        }
                        errs()<<"\n";
                }
        }


	void print_result(){
		
		int inner = -1;
		int outer = -1;
		int aa = 0;
		int kk = 0;
		std::set<int>::iterator it, it_outer, it_inner;
		for (it=set.begin(); it != set.end(); it++){
			
			list<int>::iterator it_ll;
			aa =0;
			for(it_ll=VV[*it].begin();it_ll != VV[*it].end();it_ll++){
				aa += block_sizes[*it_ll];
			}
//			errs()<< "Loop " << *it <<":   "<<loops_sizes[*it]<<" basic blocks; "<< aa <<" instructions \n"; 
			kk++;
		} 
		errs()<<"\n";
		kk = 0;
		int jj = 0;

		for (it_outer=set.begin(); it_outer != set.end(); it_outer++){
                        for (it_inner=set.begin(); it_inner != set.end(); it_inner++){
                                if(*it_inner > *it_outer){
                                        if(nested_loop_detector(*it_inner, *it_outer) == 1){

                                                if(perfect_loop_detector(*it_outer,*it_inner)){
                                                        errs() << "loop "<< *it_inner << " is nested within loop "<< *it_outer<<". Perfectly Nested\n\n";
							dependency_check(*it_outer, *it_inner);
                                                }
                                                else{
                                                        errs() << "loop "<< *it_inner << " is nested within loop "<< *it_outer<<". Not Perfectly Nested\n\n";
                                                }
                                        }
                                }
                                kk++;
                        }
                        jj++;
                }

	}
};

struct SkeletonPass : public FunctionPass {
	static char ID;
//	const char* opcode[2000];
//        int    operands[2000][10];
//        int    opcode_index = 0;

	SkeletonPass() : FunctionPass(ID) {
		for(int i=0; i< 2000; i++){
			for(int j=0;j<10;j++){
				operands[i][j]=-1;
			}
		} 
	}
	

	void test(){
		for(int i=0; i < opcode_index; i++){
			errs()<< opcode[i]<<" : ";
			for(int j = 0; j < 10;j++)
				errs()<<" "<<operands[i][j];
			errs()<<"\n";
		}
		errs()<<"it is end of test\n";
	}



	void parse_instructions(int block_index, Instruction *I){

		int operand_count = I->getNumOperands();
		operands[opcode_index][0] = block_index; //block index

		opcode[opcode_index] = I->getOpcodeName(I->getOpcode());
		const char *opcode = I->getOpcodeName(I->getOpcode());

		if(!strcmp(opcode,"alloca"))
			operands[opcode_index][1] = 0;
		else if(!strcmp(opcode,"load"))
			operands[opcode_index][1] = 1;
		else if(!strcmp(opcode,"store"))
			operands[opcode_index][1] = 2;
		else if(!strcmp(opcode,"icmp"))
			operands[opcode_index][1] = 3;
		else if(!strcmp(opcode,"br"))
			operands[opcode_index][1] = 4;
		else if(!strcmp(opcode,"add"))
			operands[opcode_index][1] = 5;
		else if(!strcmp(opcode,"sub"))
			operands[opcode_index][1] = 6;
		else if(!strcmp(opcode,"mul"))
			operands[opcode_index][1] = 7;
		else if(!strcmp(opcode,"dev"))
			operands[opcode_index][1] = 8;
		else if(!strcmp(opcode,"sext"))
			operands[opcode_index][1] = 9;
		else if(!strcmp(opcode,"getelementptr"))
			operands[opcode_index][1] = 10;
		if(!strcmp(opcode,"ret"))
			operands[opcode_index][1] = 11;
		//                      else if(!strcmp(opcode,""))
	        //                     operands[opcode_index][1] = ;
		
		char c;
		int result;
		std::string tmp;
		std::stringstream ss;
		raw_string_ostream OS(tmp);
		I->printAsOperand(OS, false);
		ss << OS.str();
		ss >> c >> result;
		operands[opcode_index][2] = result; // register holding result of peration

		for(int i=0; i < operand_count;i++){
			std::string tmp1, s;
			int operand;
			char c1;
			std::stringstream ss1,ss2;

			raw_string_ostream OS_instruction(tmp1);
			value_star_map[opcode_index][i] = I->getOperand(i); // To do the changes in instructions.
			I->getOperand(i)->printAsOperand(OS_instruction,false);
			ss1 << OS_instruction.str();
			ss1 >> s;
			ss2 << s;
			if(s.at(0)=='%'){
				ss2 >> c1 >> operand; //This is the block number
			}
			else{
				ss2 >> operand;
			}
			operands[opcode_index][i+3] = operand ;
		}
		opcode_index++;
	}


	virtual bool runOnFunction(Function &F) {
		int block_count = 0;
		int block_index = -1;
		int block_current;
		unordered_map<int,int> block_map;
		unordered_map<int,int> reverse_block_map;
		unordered_map<int,int>::const_iterator it_map, it_map1;
		list<int>  blocks[1000];
		//				int block_sizes[1000];

		for (auto& B : F) {
			int size_of_block = 0;
			std::string tmp;
			int label;		
			char c;	
			std::stringstream ss;
			raw_string_ostream OS_block(tmp);

			B.printAsOperand(OS_block, false);
			ss << OS_block.str();
			ss >> c >> label; //This is the block number
			it_map = block_map.find(label); 
			if(it_map == block_map.end())
					{
						block_index++;
						block_count++;
						std::pair<int, int> pair1(label, block_index);
						std::pair<int, int> pair2(block_index,label);
						block_map.insert(pair1);
						reverse_block_map.insert(pair2);
						block_current = block_index;
					}
					else{
						block_current = it_map->second;
					}
					for (auto& I : B){
						parse_instructions(block_index,&I);
						size_of_block++;
						if(!strcmp(I.getOpcodeName(I.getOpcode()),"br")) {

							int operand_count = I.getNumOperands();
							int i = 0;
							if(operand_count == 3 )
								i = 1;
							for(; i< operand_count ;i++){
								std::string tmp1;
								int label1;		
								char c1;	
								std::stringstream ss1;
								raw_string_ostream OS_instruction(tmp1);
								I.getOperand(i)->printAsOperand(OS_instruction,false);
								ss1 << OS_instruction.str();
								ss1 >> c1 >> label1; //This is the blocki number
								it_map1 = block_map.find(label1);  
								if(it_map1 == block_map.end()){	
									block_index++;
									block_count++;
									std::pair<int, int> pair3(label1,block_index);
									std::pair<int, int> pair4(block_index,label1);
									block_map.insert(pair3);
									reverse_block_map.insert(pair4);		
									blocks[block_current].push_back(block_index);
								}
								else{
									blocks[block_current].push_back(it_map1->second);
								}
							}
						}
					}
					block_sizes[block_current] = size_of_block;
				}

				LoopManager *lp = new LoopManager(block_count, blocks);//,block_sizes);
				list<int>::iterator it;			
				for(int i=0; i < block_count;i++){
					for(it=blocks[i].begin(); it != blocks[i].end(); it++){
						lp->add_edge(i,*it);			  
					}
				}
//				errs()<<"Function name is :"<<F.getName()<<"\n";
				lp->DFS();
				//lp->print_loops();
				lp->print_result();	
			
				errs()<<"Function name: "<<F.getName()<<"\n";	
				for (auto& B : F) {
					std::string tmp;		
					int blk_ind = -1;
					int blk_ind_1 = -1;
					int label;		
					char c;	
					Value* val_tmp;
					Value* val_tmp1;
					Value* val_tmp2;
					int val_index = -1;
					

					std::stringstream ss;
					raw_string_ostream OS_block(tmp);

					B.printAsOperand(OS_block, false);
					ss << OS_block.str();
					ss >> c >> label; //This is the block number
					auto search = block_map.find(label);
					if(search != block_map.end())
						blk_ind = search->second;
					int chg_ind = 0;	
					for(chg_ind; chg_ind < index_changes; chg_ind++){
						if(instruction_changes[chg_ind][0] == blk_ind || instruction_changes[chg_ind][1] == blk_ind){
							if(instruction_changes[chg_ind][2] == 1 && instruction_changes[chg_ind][0] == blk_ind){	
								blk_ind_1 = instruction_changes[chg_ind][0];
							}
							else if(instruction_changes[chg_ind][2] == 1 && instruction_changes[chg_ind][1] == blk_ind){	
								blk_ind_1 = instruction_changes[chg_ind][1];
							}

							else if(instruction_changes[chg_ind][2] == 3){
								if(instruction_changes[chg_ind][0] == blk_ind){
									blk_ind_1 = instruction_changes[chg_ind][1];
								}
								else if(instruction_changes[chg_ind][1] == blk_ind){
									blk_ind_1 = instruction_changes[chg_ind][0];
								}
							}
							for(int i=0; i < opcode_index; i++){
								if(operands[i][0] == blk_ind_1){
									//errs()<<"bbbb instruction_changes[i][2] "<<instruction_changes[chg_ind][2]<<" operands[i][1] "<<operands[i][1]<<" i : "<<i<<" chg_ind "<<chg_ind<<"\n";
									if(instruction_changes[chg_ind][2] == 3 && operands[i][1] == 3){
										val_tmp = value_star_map[i][1]; //The const value of icmp
										break;
									}
									else if (instruction_changes[chg_ind][2] == 1 && operands[i][1] == 1){
										if(instruction_changes[chg_ind][0] == blk_ind_1 &&  operands[i][3] == instruction_changes[chg_ind][4]){
											val_tmp1 = value_star_map[i][0];
										}
										else if(instruction_changes[chg_ind][1] == blk_ind_1 && operands[i][3] == instruction_changes[chg_ind][5]){
											val_tmp2 = value_star_map[i][0]; 
										}
									}
								}
							}
						
							for (auto& I : B){
								if(!strcmp(I.getOpcodeName(I.getOpcode()),"icmp")){	
									I.setOperand(1,val_tmp);
								}
								else if(!strcmp(I.getOpcodeName(I.getOpcode()),"load") && I.getOperand(0) == val_tmp1){
									I.setOperand(0,val_tmp2);
								}
								else if(!strcmp(I.getOpcodeName(I.getOpcode()),"load") && I.getOperand(0) == val_tmp2){
									I.setOperand(0,val_tmp1);
								}
							}
						}
					}
					B.print(errs());
								}

				return false;
	}
}; // end of class pass
}//end of namespace

		char SkeletonPass::ID = 0;

		// Automatically enable the pass.
		// http://adriansampson.net/blog/clangpass.html
		static void registerSkeletonPass(const PassManagerBuilder &,
				legacy::PassManagerBase &PM) {
			PM.add(new SkeletonPass());
		}
		static RegisterStandardPasses
			RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
				registerSkeletonPass);
