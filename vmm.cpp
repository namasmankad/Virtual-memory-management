#include <iomanip>
#include <iostream>
#include <sstream>
#include <fstream>
#include <list>
#include <istream>
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include <string>
#include <vector>
#include <limits.h>
#include <cstring>

using namespace std;

bool oflag = false;
bool pflag = false;
bool fflag = false;
bool sflag = false;


unsigned int ctx_switch_cost = 130;
unsigned int maps_cost = 300;
unsigned int unmaps_cost = 400;
unsigned int ins_cost = 3100;
unsigned int outs_cost = 2700;
unsigned int fins_cost = 2800;
unsigned int fouts_cost = 2400;
unsigned int zeros_cost = 140;
unsigned int segv_cost = 340;
unsigned int segprot_cost = 420;
// unsigned int access_cost = 1;
unsigned int process_exit_cost = 1250;
int num_vma = 0;
int num_proc = 0;
int page_t_size = 64;
int frame_t_size = 16;

unsigned long instr_count=0;
unsigned long proc_exits=0;
unsigned long ctx_switches=0;
unsigned long total_cycles=0;
unsigned long long total_cost=0;

int algo;
const int FIFO = 1;
const int RANDOM = 2;
const int CLOCK = 3;
const int ESCN = 4;
const int AGING = 5;
const int WORKING = 6;

vector<int> random_list;
vector<int> store_processid;
vector<int> store_frameid;

class VMA
{
public:
	int start_vpage;
	int end_vpage;
	int write_protected;
	int file_mapped;
};

//typedef
struct PTE
{
	// public:
		unsigned int present:1;
	    unsigned int referenced:1;
	    unsigned int modified:1;
	    unsigned int write_protect:1;
	    unsigned int pagedout:1;
	    unsigned int frame_number:7;
	    unsigned int padding:20;
	    PTE()
	    {
	    	this->present = 0;
	    	this->referenced = 0;
	    	this->modified = 0;
	    	this->write_protect = 0;
	    	this->pagedout = 0;
	    	this->frame_number = 0;
	    	this->padding = 0;
	    }
}pte_t;

class Process
{
	public:
		int pid;
		vector<VMA*> vmas;
		vector<PTE*> ptes;
		unsigned long unmaps = 0;
		unsigned long maps = 0;
		unsigned long ins = 0;
		unsigned long outs = 0;
		unsigned long fins = 0;
		unsigned long fouts = 0;
		unsigned long zeros = 0;
		unsigned long segv = 0;
		unsigned long segprot = 0;
};

struct Frame
{
	int frameid;
	unsigned long age;
	unsigned long tau;
	bool eflag;
	int revmap1;
	int revmap2;
};

// struct FrameT
// {
	vector<Frame*> frame_list;
	list<Frame*> free_pool;
// };

struct Instruction
{
	char instr;
	int addr;
};

vector<Instruction> instructions;
vector<Process*> all_processes;
int rnum;
// list<Frame*> pager_frame;

class PageRep
{
	public:
		list<Frame*> pager_frame; //make global???
		virtual Frame* select_victim_frame(vector<Frame*> frame_list, list<Frame*> free_pool, unsigned long instrid) = 0;
};

class FIFOPageRep : public PageRep
{
	public:
		Frame* select_victim_frame(vector<Frame*> frame_list, list<Frame*> free_pool, unsigned long instrid)
		{
			if (pager_frame.empty())
			{
				return nullptr;
			}
			else
			{
				Frame* f_temp = pager_frame.front();
				pager_frame.pop_front();
				store_frameid.push_back(f_temp->frameid);////////////
				return f_temp;
			}
		}
};

class RandomPageRep : public PageRep
{
	public:
		Frame* select_victim_frame(vector<Frame*> frame_list, list<Frame*> free_pool, unsigned long instrid)
		{
			if(pager_frame.empty())
			{
				return nullptr;
			}
			else
			{
				int rkey = rnum % random_list.size();
				rnum++;
				int ridx = random_list[rkey] % frame_list.size();
				Frame* f1 = frame_list[ridx];
				store_frameid.push_back(f1->frameid);////////////
				return f1;
			}
		}
};

class ClockPageRep : public PageRep
{
	public:
		Frame* select_victim_frame(vector<Frame*> frame_list, list<Frame*> free_pool, unsigned long instrid)
		{
			bool temp_flag = true;
			bool temp_flag1 = true;

			if(pager_frame.empty())
			{
				return nullptr;
			}
			else
			{
				Frame* cur_frame = pager_frame.front();
				Process* cur_process = all_processes[cur_frame->revmap1];
				PTE* cur_pte = cur_process->ptes[cur_frame->revmap2];
				store_processid.push_back(cur_process->pid);////////////////

				while (cur_pte->referenced == 1)
				{
					cur_pte->referenced = 0;
					pager_frame.pop_front();
					pager_frame.push_back(cur_frame);
					cur_frame = pager_frame.front();
					cur_process = all_processes[cur_frame->revmap1];
					cur_pte = cur_process->ptes[cur_frame->revmap2];
				}
				temp_flag = false;

				pager_frame.pop_front();

				if(temp_flag1 == true)
				{
					while(cur_frame->eflag)
					{
						cur_frame->eflag = false;
						cur_frame = select_victim_frame(frame_list, free_pool, instrid);
					}
					temp_flag1=false;
				}
				store_frameid.push_back(cur_frame->frameid);////////////
				return cur_frame;
			}
		}
};

class ESCNPageRep : public PageRep
{
	public:
		Frame* p_frame[4];
		int h;
		unsigned long ins1 = 0;

		Frame* select_victim_frame(vector<Frame*> frame_list, list<Frame*> free_pool, unsigned long instrid)
		{
			Frame* cur_frame;
			Frame* v_frame = nullptr;
			Process* cur_process;
			PTE* cur_pte;
			int idx;

			p_frame[2] = nullptr;
			p_frame[0] = nullptr;
			p_frame[3] = nullptr;
			p_frame[1] = nullptr;

			for(int i = 0; i< frame_list.size(); i++)
			{
				int fidx = (i+h) % frame_list.size();
				cur_frame = frame_list[fidx];
				cur_process = all_processes[cur_frame->revmap1];
				cur_pte = cur_process->ptes[cur_frame->revmap2];
				idx = cur_pte->modified + cur_pte->referenced * 2;
				store_frameid.push_back(cur_frame->frameid);////////////
				store_processid.push_back(cur_process->pid);

				if(p_frame[idx] == nullptr)
				{
					if(idx == 0)
					{
						v_frame = cur_frame;
						h = (fidx + 1) % frame_list.size();
						break;
					}
					p_frame[idx] = cur_frame;
				}
			}
			if(!v_frame)
			{
				if(p_frame[1] != nullptr)
				{
					v_frame = p_frame[1];
					h = (v_frame->frameid + 1) % frame_list.size();
				}
				else if(p_frame[2] != nullptr)
				{
					v_frame = p_frame[2];
					h = (v_frame->frameid + 1) % frame_list.size();
				}
				else if(p_frame[3] != nullptr)
				{
					v_frame = p_frame[3];
					h = (v_frame->frameid + 1) % frame_list.size();
				}
			}
			bool pid_check = true;
			if(instrid - ins1 >= 50)
			{
				for(auto fr: frame_list)
				{
					cur_frame = fr;
					int p_id = cur_frame->revmap1;
					if(!(p_id == -1) && (pid_check))
					{
						all_processes[p_id]->ptes[cur_frame->revmap2]->referenced = 0;
					}
				}
				ins1 = instrid;
			}
			store_frameid.push_back(v_frame->frameid);////////////
			return v_frame;
		}
};

class AgingPageRep : public PageRep
{
	public:
		int h = 0;
		Frame* select_victim_frame(vector<Frame*> frame_list, list<Frame*> free_pool, unsigned long instrid)
		{
			Frame* cur_frame;
			Frame* v_frame;
			Process* cur_process;
			PTE* cur_pte;
			v_frame = frame_list[h];

			for(int i=0;i<frame_t_size; i++)
			{
				int idx = (i + h) % frame_list.size();
				cur_frame = frame_list[(idx)];
				cur_process = all_processes[cur_frame->revmap1];
				cur_pte = cur_process->ptes[cur_frame->revmap2];
				store_frameid.push_back(cur_frame->frameid);////////////
				store_processid.push_back(cur_process->pid);

				cur_frame->age = cur_frame->age >> 1;
				if (cur_pte->referenced)
				{
					cur_frame->age = cur_frame->age | ((unsigned long) 1 << 31);
				}
				cur_pte->referenced = 0;
				if(cur_frame->age < v_frame->age)
				{
					v_frame = cur_frame;
				}
			}
			h = (v_frame->frameid + 1) % frame_t_size;
			store_frameid.push_back(v_frame->frameid);////////////
			return v_frame;
		}
};

class WorkingPageRep : public PageRep
{
	public:
		int h = 0;
		Frame* select_victim_frame(vector<Frame*> frame_list, list<Frame*> free_pool, unsigned long instrid)
		{
			int maxdif = INT_MIN;
			Frame* cur_frame;
			Frame* v_frame = nullptr;
			Process* cur_process;
			PTE* cur_pte;
			//h = 0;
			bool diffcheck=true;

			for(int i =0; i<frame_t_size; i++)
			{
				int idx = (h + i) % frame_list.size();
				cur_frame = frame_list[(h + i) % frame_list.size()];
				cur_process = all_processes[cur_frame->revmap1];
				cur_pte = cur_process->ptes[cur_frame->revmap2];
				store_frameid.push_back(cur_frame->frameid);////////////
				store_processid.push_back(cur_process->pid);
				if(diffcheck)
				{
					if(cur_pte->referenced == 0)
					{
						int dif1 = instrid - cur_frame->tau - 1;
						int dif2 = dif1 - cur_frame->tau;
						if(dif1 >= 50 || dif1 > maxdif)
						{
							v_frame = cur_frame;
							if(dif1 >= 50)
							{
								break;
							}
							if (dif1 > maxdif && dif1 < 50)
							{
								diffcheck = true;
								maxdif = dif1;
							}
						}
					}
					else
					{
						cur_frame->tau = instrid - 1;
					}
				}
				cur_pte->referenced = 0;
			}

			diffcheck = false;
			if (v_frame == nullptr)
			{
				v_frame = frame_list[h];
			}

			h = (1 + v_frame->frameid) % frame_list.size();
			store_frameid.push_back(v_frame->frameid);////////////
			return v_frame;
		}
};

bool fileMappedCheck(Process* proc, int virtualPageIndex)
{
	bool temp = true;
	while(temp = true) 
	{
		for(auto it: proc->vmas)
		{
			if(virtualPageIndex <= it->end_vpage && virtualPageIndex >= it->start_vpage)
			{
				if (it->file_mapped == 0)
				{
					return false;
				}
				else if (it->file_mapped != 0)
				{
					return true;
				}
			}
		} 
		temp = false;
	}
	return false;
}


PageRep* p_rep;

int main(int argc, char *argv[])
{
	string inputfile;
	string randomfile;
	// PageRep* prep;??
	string str;
	string str1;
	int c;
	while((c = getopt(argc, argv, "a:o:f:")) != -1)
	{
		switch(c)
		{
			case 'a':
			{
				switch(optarg[0])
				{
					case 'f':
					{
						p_rep = new FIFOPageRep();
						algo = FIFO;
						break;
					}
					case 'r':
					{
						p_rep = new RandomPageRep();
						algo = RANDOM;
						break;
					}
					case 'c':
					{
						p_rep = new ClockPageRep();
						algo = CLOCK;
						break;
					}
					case 'e':
					{
						p_rep = new ESCNPageRep();
						algo = ESCN;
						break;
					}
					case 'a':
					{
						p_rep = new AgingPageRep();
						algo = AGING;
						break;
					}
					case 'w':
					{
						p_rep = new WorkingPageRep();
						algo = WORKING;
						break;
					}
					default:
					{
						abort();
					}
				}
				break;
			}
			case 'o':
			{
				str = optarg;
				int i = str.size()-1;
				while(i>=0)
				{
					if (str[i] == 'O')
					{
						oflag = true;
					}
					else if (str[i] == 'P')
					{
						pflag= true;
					}
					else if (str[i] == 'F')
					{
						fflag = true;
					}
					else if (str[i] == 'S')
					{
						sflag = true;
					}
					i -= 1;
				}
				break;
			}
			case 'f':
			{
				str1 = optarg;
				if (!str1.empty())
				{
					frame_t_size = atoi(str1.c_str());
				}
				break;
			}
			default:
			{
				abort();
			}
		}
	}
	inputfile = argv[optind];
	randomfile = argv[optind+1];

	// cout<<frame_t_size<<endl;

	if(algo == RANDOM)
	{
		ifstream random_file;
		int rfile_size, rvalues;
		random_file.open(randomfile);
		random_file>>rfile_size;
		while(random_file >> rvalues)
		{
			random_list.push_back(rvalues);
		}
		random_file.close();
	}

	ifstream input_file;
	input_file.open(inputfile);
	string buffer;
	int num_proc2 = 0;
	int cnt = 1;

	while(getline(input_file, buffer))
	{
		// getline(input_file, buffer);
		char cur_string;
		stringstream token(buffer);
		token >> cur_string;
		if(cur_string == '#')
		{
			// cout<<cur_string<<endl;
			continue;
		}
		if(cnt == 1)
		{
			num_proc = stoi(buffer); //stoi(&buffer[0]);
			// cout<<num_proc<<endl;///////
			cnt = 2;
			// num_proc2 = num_proc;
		}
		else if(cnt == 2 && num_proc2 < num_proc)
		{
			num_vma = stoi(buffer); //stoi(&buffer[0]);
			// cout<<num_vma<<endl;/////////////
			Process* p_temp = new Process();
			p_temp->pid = num_proc2;
			p_temp->unmaps = 0;
			p_temp->maps = 0;
			p_temp->ins = 0;
			p_temp->outs = 0;
			p_temp->fins = 0;
			p_temp->fouts = 0;
			p_temp->zeros = 0;
			p_temp->segv = 0;
			p_temp->segprot = 0;

			for(int i=0; i< page_t_size; i++)
			{
				p_temp->ptes.push_back(new PTE());
			}

			for(int i=0; i< num_vma; i++)
			{
				getline(input_file, buffer);
				stringstream tok(buffer);
				string a1,a2,a3,a4;
				tok>>a1>>a2>>a3>>a4;
				VMA* v_temp = new VMA();
				// cout<<a1<<a2<<a3<<a4<<endl;//////////
				v_temp->start_vpage = stoi(a1);
				v_temp->end_vpage = stoi(a2);
				v_temp->write_protected = stoi(a3);
				v_temp->file_mapped = stoi(a4);
				p_temp->vmas.push_back(v_temp);
			}
			all_processes.push_back(p_temp);
			num_proc2 += 1;
			// if(num_proc2 > num_proc)
			// {
			// 	cnt = 3;
			// 	// continue; //??
			// }
		}
		else //if(cnt==3)
		{
			// if(buffer[0] == '#')
			// {
			// 	continue;
			// }
			// if(buffer[0]!='#') {
				// cout<<"yo"<<endl;
				Instruction i_temp;
				// char *pch;
				// pch = strtok(&buffer[0], " ");
				// i_temp.instr = *pch;
				// pch = strtok(NULL, " ");
				// i_temp.addr = atoi(pch);
				stringstream tok(buffer);
				string b1, b2;
				tok>>b1>>b2;
				i_temp.instr = b1[0];
				i_temp.addr = stoi(b2);
				// cout<<i_temp.instr<<i_temp.addr<<endl;
				instructions.push_back(i_temp);
			// }
		}
	}

	input_file.close();
	//inputs taken

	//simulation
	string op; //operation
	int vp; //vpage
	Process* process = nullptr;

	//fill the frame list and free pool
	for(int i =0; i< frame_t_size; i++)
	{
		Frame* f_temp = new Frame(); //auto* ??
		f_temp->frameid = i;
		f_temp->age = 0;
		f_temp-> eflag = false;
		f_temp->tau = 0;
		f_temp->revmap1 = -1;
		f_temp->revmap2 = -1;
		frame_list.push_back(f_temp);
		free_pool.push_back(f_temp);
	}


	for(int i=0; i<instructions.size(); i++)
	{
		op = instructions[i].instr;
		vp = instructions[i].addr;

		// cout<<"op vp :"<<op<<" "<<vp<<endl;

		if(oflag == true)
		{
			cout<<instr_count<<": ==> "<<op<<" "<<vp<<endl;
		}

		instr_count += 1;

		bool cflag = false;
		if(op == "c")
		{
			process = all_processes[vp];
			total_cycles += 1;
			ctx_switches += 1;
			total_cost += ctx_switch_cost;
		}
		else if(op == "r" || op == "w")
		{
			total_cycles += 1;
			total_cost += 1;
			cflag = false;
			for(int j=0; j<process->vmas.size(); j++)
			{
				if(process->vmas[j]->start_vpage <= vp && vp <= process->vmas[j]->end_vpage)
				{
					cflag = true;
					break;
				}
			}
			if (cflag == true)
			{
				PTE* pte_temp = process->ptes[vp];
				Frame* current_frame = nullptr;
				if(pte_temp->present) // if(pte_temp->present)??
				{
					current_frame = frame_list[pte_temp->frame_number];
				}
				else
				{
					if(free_pool.size() > 0)
					{
						Frame* frame_temp = free_pool.front();
						free_pool.pop_front(); //free_pool.erase(free_pool.begin());
						current_frame = frame_temp;
					}
					else
					{
						current_frame = nullptr;
					}
					if(current_frame == nullptr)
					{
						current_frame = p_rep->select_victim_frame(frame_list, free_pool, instr_count);
						Process* old_process = all_processes[current_frame->revmap1];
						PTE* old_pte = old_process->ptes[current_frame->revmap2];
						old_process->unmaps += 1;
						old_pte->present = 0;
						old_pte->referenced = 0;
						total_cycles += 1;
						total_cost += unmaps_cost;
						if(oflag == true)
						{
							cout<<" UNMAP "<<current_frame->revmap1<<":"<<current_frame->revmap2<<endl;
						}
						if(old_pte->modified) //if(old_pte->modified)
						{
							old_pte->modified = 0;
							if(fileMappedCheck(old_process, current_frame->revmap2))
							{
								old_process->fouts += 1;
								total_cycles += 1;
								total_cost += fouts_cost;
								if(oflag == true)
								{
									cout<<" FOUT"<<endl;
								}
							}
							else
							{
								old_process->outs += 1;
								old_pte->pagedout = 1;
								total_cycles += 1;
								total_cost += outs_cost;
								if (oflag == true)
								{
									cout<<" OUT"<<endl;
								}
							}
						}
					}
					else///////////////
					{
						store_frameid.push_back(current_frame->frameid);
					}
					///////////
					for(int a = 0; a<all_processes.size(); a++)
					{
						store_processid.push_back(a);
					}

					if(fileMappedCheck(process, vp))
					{
						process->fins += 1;
					}
					if(!(fileMappedCheck(process, vp)) && pte_temp->pagedout)
					{
						process->ins += 1;
					}
					if(!(fileMappedCheck(process, vp)) && !pte_temp->pagedout)
					{
						process->zeros += 1;
					}
					if(oflag == true)
					{
						if(fileMappedCheck(process, vp))
						{
							cout<<" FIN"<<endl;
						}
						else 
						{
							if(pte_temp->pagedout) //else if(pte_temp-pagedout)
							{
								cout<<" IN"<<endl;
							}
							else
							{
								cout<<" ZERO"<<endl;
							}
						}
					}
					if(fileMappedCheck(process, vp))
					{
						total_cost += fins_cost;
					}
					else
					{
						if(pte_temp->pagedout)
						{
							total_cost += ins_cost;
						}
						else
						{
							total_cost += zeros_cost;
						}
					}
					total_cycles += 1;
					for(int a = 0; a<all_processes.size(); a++)////////
					{
						store_processid.push_back(a);
					}
					current_frame->revmap1 = process->pid;
					current_frame->revmap2 = vp;
					pte_temp->frame_number = current_frame->frameid;///

					for(int a = 0; a<frame_list.size(); a++)////////
					{
						store_processid.push_back(a);
					}
					pte_temp->present = 1;
					total_cycles += 1;
					total_cost += maps_cost;
					process->maps += 1;
					current_frame->age = 0;

					if(current_frame->eflag != true)
					{
						p_rep->pager_frame.push_back(current_frame);
					}
					else
					{
						current_frame->eflag = false;
					}
					if(oflag == true)
					{
						cout<<" MAP "<<current_frame->frameid<<endl;
					}
				}
				pte_temp->referenced = 1;
				current_frame->tau = instr_count - 1;

				if(op == "w")
				{
					bool temp_flag = false;
					for(int idx = 0; idx < process->vmas.size(); idx++)
					{
						if(vp >= process->vmas[idx]->start_vpage && vp <= process->vmas[idx]->end_vpage)
						{
							if(process->vmas[idx]->write_protected == 0)
							{
								temp_flag = false;
							}
							else
							{
								temp_flag = true;
							}
						}
					}
					if (temp_flag == true)
					{
						process->segprot += 1;
						total_cycles += 1;
						total_cost += segprot_cost;
						if(oflag == true)
						{
							cout<<" SEGPROT"<<endl;
						}
					}
					else
					{
						pte_temp->modified = 1;
					}
				}
			}
			else
			{
				process->segv += 1;
				if (oflag == true)
				{
					cout<<" SEGV"<<endl;
				}
				for(int a = 0; a<all_processes.size(); a++)
				{
					store_processid.push_back(a);
				}
				total_cost += segv_cost;
				continue;
			}
		}
		else if (op == "e")
		{
			proc_exits += 1;
			total_cycles += 1;
			total_cost += process_exit_cost;
			if(oflag == true)
			{
				cout<<"EXIT current process "<<vp<<endl;
			}
			for(int j=0; j<page_t_size; j++)
			{
				PTE* current_pte = process->ptes[j];
				if(current_pte->present)//if(current_pte->present)??
				{
					free_pool.push_back(frame_list[current_pte->frame_number]);
					Frame* current_frame = frame_list[current_pte->frame_number];

					if(oflag == true)
					{
						cout<<" UNMAP "<<current_frame->revmap1<<":"<<current_frame->revmap2<<endl;
					}

					current_frame->eflag = true;
					current_frame->revmap2 = -1;
					current_frame->revmap1 = -1;

					for(int a = 0; a<all_processes.size(); a++)
					{
						store_processid.push_back(a);
					}

					process->unmaps += 1;
					total_cycles += 1;
					total_cost += unmaps_cost;

					if(fileMappedCheck(process, j) && current_pte->modified)
					{
						total_cost += fouts_cost;
						total_cycles += 1;
						process->fouts += 1;
						
						if(oflag == true)
						{
							cout<<" FOUT"<<endl;
						}
					}
					current_pte->referenced = 0;
					current_pte->modified = 0;
					current_pte->present = 0;
				}

				current_pte->pagedout = 0;
			}
		}
	}

	//output
	if (pflag == true)
	{
		for(int i=0; i<all_processes.size();i++)
		{
			cout<<"PT["<<all_processes[i]->pid<<"]:";
			int counter = 0;
			for(int j=0;j<all_processes[i]->ptes.size();j++)
			{
				// counter += 1;
				if (!(all_processes[i]->ptes[j]->present))
				{
					if(all_processes[i]->ptes[j]->pagedout)
					{
						cout<<" #";
					}
					else
					{
						cout<<" *";
					}
				}
				else
				{
					cout<<" "<<counter<<":";
					if(all_processes[i]->ptes[j]->referenced)
					{
						cout<<"R";
					}
					else
					{
						cout<<"-";
					}
					if(all_processes[i]->ptes[j]->modified)
					{
						cout<<"M";
					}
					else
					{
						cout<<"-";
					}
					if(all_processes[i]->ptes[j]->pagedout)
					{
						cout<<"S";
					}
					else
					{
						cout<<"-";
					}
				}
				counter += 1;
			}
			cout<<endl; //cout<<" "<<endl;
		}
	}

	if(fflag == true)
	{
		cout<<"FT:";
		for(int i=0; i<frame_list.size(); i++)
		{
			if (frame_list[i]->revmap1 != -1)
			{
				cout<<" "<<frame_list[i]->revmap1;
				cout<<":"<<frame_list[i]->revmap2;
			}
			else
			{
				cout<<" *";
			}
		}
		cout<<endl;
	}

	if(sflag == true)
	{
		for(int i =0; i<all_processes.size(); i++)
		{
			printf("PROC[%d]: U=%lu M=%lu I=%lu O=%lu FI=%lu FO=%lu Z=%lu SV=%lu SP=%lu\n",all_processes[i]->pid, all_processes[i]->unmaps, all_processes[i]->maps, all_processes[i]->ins, all_processes[i]->outs, all_processes[i]->fins, all_processes[i]->fouts, all_processes[i]->zeros, all_processes[i]->segv, all_processes[i]->segprot);
		}
	}
	// unsigned long len_pte = sizeof(pte)
	printf("TOTALCOST %lu %lu %lu %llu %lu\n", instr_count, ctx_switches, proc_exits, total_cost, sizeof(pte_t));

	return 0;
}
