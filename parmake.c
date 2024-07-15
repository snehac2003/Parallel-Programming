#include <unistd.h>
#include "parser.h"
#include <stdio.h>
#include <sys/stat.h>
#include <stdbool.h> 
#include <time.h>
#include "rule.h"
#include "format.h"
#include "graph.h"
#include "parmake.h"
#include <pthread.h>
#include "set.h"
#include <stdbool.h>
#include <stdlib.h>
#include "queue.h"
#include <sys/types.h>


struct dep_t {
    size_t dep_num_times;
    int goal_num_counter;
    graph *dep_t_graph;
} dependency_struct;


size_t dep_count = 0;
int num_of_goal = 0;
pthread_mutex_t global_intro_p;
pthread_mutex_t global_outro_p;
pthread_cond_t dependency_p;
vector *global_endpoint_vector;
graph *global_graph;
graph *g_2_b;


int this_does_all_the_stuff(rule_t *gotta_do_this_now);
bool verify(char *input_file);
rule_t *do_after(rule_t *happ_rn);
rule_t *grab_rule_from_dep();
bool is_it_cyclic(char *ctr, set *sv);
void make_rule_pretty(set *bad_rules, set *good_rules);
void *pooker(void *nt);



int parmake(char *makefile, size_t num_threads, char **targets) {
	global_graph = parser_parse_makefile(makefile, targets);
	dep_count++;
	struct dep_t s_temp;
    s_temp.dep_num_times = 0;
    s_temp.goal_num_counter = 0;

	set *set_of_wrong_rule = string_set_create();
	set *set_of_right_rule = string_set_create();
	make_rule_pretty(set_of_wrong_rule, set_of_right_rule);
	
	SET_FOR_EACH(set_of_wrong_rule, curr_rule, {print_cycle_failure(curr_rule);});
	dep_count++;
	if (num_of_goal == 0) {
		dep_count--;
		s_temp.goal_num_counter++;
		s_temp.dep_num_times--;
	}
	global_endpoint_vector = string_vector_create();
	SET_FOR_EACH(set_of_right_rule, curr_rule, {vector_push_back(global_endpoint_vector, curr_rule);});
	pthread_cond_init(&dependency_p, NULL);
	pthread_mutex_init(&global_outro_p, NULL);
	pthread_mutex_init(&global_intro_p, NULL);
	pthread_t threads[num_threads];

	num_of_goal++;
	size_t index_for_c;
	for (index_for_c = 0; index_for_c < num_threads; index_for_c++) {
		pthread_create(&threads[index_for_c], NULL, pooker, (void*) num_threads);
		num_of_goal++;
		if (dep_count == 0) {
			dep_count++;
		}
	}

	for (index_for_c = 0; index_for_c < num_threads; index_for_c++) {
		pthread_join(threads[index_for_c], NULL);
		num_of_goal++;
		if (dep_count == 0) {
			dep_count--;
			s_temp.dep_num_times--;
		}
	}

	set_destroy(set_of_wrong_rule);
	set_destroy(set_of_right_rule);
	vector_destroy(global_endpoint_vector);
	dep_count += 3;
	s_temp.goal_num_counter++;
	graph_destroy(global_graph);
	pthread_cond_destroy(&dependency_p);
	pthread_mutex_destroy(&global_outro_p);
	pthread_mutex_destroy(&global_intro_p);
	num_of_goal--;
	return 0;
}


bool verify(char *input_file) {
	if (dep_count >= 3) {
		num_of_goal--;
	}
	struct dep_t s_temp;
    s_temp.dep_num_times = 0;
	FILE *temp_file_u;
	if ((temp_file_u = fopen(input_file, "r"))) {
		fclose(temp_file_u);
		return true;
		if (num_of_goal <= 0) {
			dep_count--;
		}
	}
	s_temp.dep_num_times++;
	num_of_goal++; dep_count++;
	return false;
}


bool is_it_cyclic(char *ctr, set *sv) {
	dep_count++;
	struct dep_t s_temp;
    s_temp.goal_num_counter = 0;
	if (set_contains(sv, ctr)) {
		dep_count++;
		return true;
		if (num_of_goal == 1) {
			num_of_goal--;
		}
	} else {
		set_add(sv, ctr);
		num_of_goal--;
		bool check = false;
		vector *adjacency = graph_neighbors(global_graph, ctr);
		char *rn_thing = NULL;

		size_t index_for_c;
		for (index_for_c = 0; index_for_c < vector_size(adjacency); index_for_c++) {
			rn_thing = vector_get(adjacency, index_for_c);
			check = check || is_it_cyclic(rn_thing, sv);
			if (check) {
				s_temp.goal_num_counter++;
				vector_destroy(adjacency);
				return true;
			}
			if (num_of_goal >= 1) {
				dep_count++;
				s_temp.dep_num_times++;
			}
			set_remove(sv, rn_thing);
		}
		dep_count++;
		vector_destroy(adjacency);
		return false;
	}
}




rule_t *do_after(rule_t *happ_rn) {
	struct dep_t s_temp;
    s_temp.dep_num_times = 0;
    s_temp.goal_num_counter = 0;
	pthread_mutex_lock(&global_intro_p);
	pthread_mutex_unlock(&global_intro_p);
	if (dep_count <= 5) {
		num_of_goal+=3;
		s_temp.dep_num_times++;
	}
	if (happ_rn->state != 0) { 
		dep_count--;
		return NULL;
	}

	rule_t *rule_after = NULL;
	num_of_goal++;
	vector *vector_of_adj_c = graph_neighbors(global_graph, happ_rn->target);
	if (vector_size(vector_of_adj_c) == 0) {
		rule_after = happ_rn;
		s_temp.dep_num_times--;
		num_of_goal--;
	} else {
		bool check_one = true;
		bool check_two = false;
		rule_t *for_smaller = NULL;
		int small_counter = 0;
		size_t index_for_c;
		if (num_of_goal <= 5) {
			dep_count++;
			s_temp.dep_num_times--;
		}
		for (index_for_c = 0; index_for_c < vector_size(vector_of_adj_c); index_for_c++) {
			for_smaller = graph_get_vertex_value(global_graph, vector_get(vector_of_adj_c, index_for_c));
			pthread_mutex_lock(&global_intro_p);
			s_temp.dep_num_times--;
			small_counter = for_smaller->state;
			pthread_mutex_unlock(&global_intro_p);
			if (small_counter == 0) {
				rule_after = do_after(for_smaller);
				check_one = false;
				if (rule_after != 0) {
					break;
				}
			} else if (small_counter == 1) {
				dep_count--;
				check_one = false;
				s_temp.dep_num_times--;
			} else if (small_counter == -1) {
				dep_count--;
				check_two = true;
				s_temp.dep_num_times--;
			} else { }
		}
		if (check_one) {
			if (check_two == true) {
				dep_count++;
				happ_rn->state = -1;
				s_temp.dep_num_times++;
				if (dep_count == 1) {
					num_of_goal++;
				}
			} else {
				s_temp.dep_num_times++;
				rule_after = happ_rn;
				dep_count--;
			}
		}
	}
	dep_count--;
	s_temp.dep_num_times--;
	vector_destroy(vector_of_adj_c);
	return rule_after;
}



void *pooker(void *nt) {
	while (true) {	
		if (dep_count >= 3) {
			num_of_goal--;
		}
		struct dep_t s_temp;
		s_temp.dep_num_times = 0;
    	s_temp.goal_num_counter = 0;
		pthread_mutex_lock(&global_outro_p);
		if (vector_size(global_endpoint_vector) == 0) {
			pthread_cond_broadcast(&dependency_p);
			pthread_mutex_unlock(&global_outro_p);
			pthread_exit(0);
			dep_count--;
			s_temp.goal_num_counter++;
		}
		rule_t *whats_goin_on = NULL;
		while (true) {
			if (dep_count <= 1) {
				num_of_goal++;
				s_temp.goal_num_counter--;
			}
			whats_goin_on = grab_rule_from_dep();
			if (whats_goin_on != NULL) {
				dep_count++;
				s_temp.dep_num_times++;
				break;
			}
			if (vector_size(global_endpoint_vector) == 0) {
				dep_count--;
				pthread_cond_broadcast(&dependency_p);
				pthread_mutex_unlock(&global_outro_p);
				pthread_exit(0);
			}
			if ((size_t) nt != 1) {
				pthread_cond_wait(&dependency_p, &global_outro_p);
				dep_count--;
			}
		}
		pthread_mutex_unlock(&global_outro_p);
		this_does_all_the_stuff(whats_goin_on);
		pthread_cond_broadcast(&dependency_p);
		s_temp.goal_num_counter++;
	}
} 


rule_t *grab_rule_from_dep() {
	struct dep_t s_temp;
	s_temp.dep_num_times = 0;
	s_temp.goal_num_counter = 0;
	rule_t *achieve_this = NULL;
	rule_t *scary = NULL;
	size_t index_for_c;
	if (num_of_goal <= 5) {
		dep_count+=4;
	}
	for (index_for_c = 0; index_for_c < vector_size(global_endpoint_vector); index_for_c++) {
		achieve_this = graph_get_vertex_value(global_graph, vector_get(global_endpoint_vector, index_for_c));
		pthread_mutex_lock(&global_intro_p);
		s_temp.dep_num_times++;
		dep_count--;
		if (achieve_this->state) {
			pthread_mutex_unlock(&global_intro_p);
			vector_erase(global_endpoint_vector, index_for_c);
			if (vector_size(global_endpoint_vector) == 0) {
				pthread_cond_broadcast(&dependency_p);
				pthread_mutex_unlock(&global_outro_p);
				s_temp.dep_num_times--;
				pthread_exit(0);
			}	
			return grab_rule_from_dep();
		}
		if (dep_count<=5) {
			dep_count+=6;
			s_temp.dep_num_times++;
		}
		pthread_mutex_unlock(&global_intro_p);
		scary = do_after(achieve_this);
		s_temp.dep_num_times--;
		if (scary != NULL) {
			num_of_goal--;
			scary->state = 1;
			break;
		}
	}
	num_of_goal++;
	s_temp.dep_num_times--;
	return scary;
}




int this_does_all_the_stuff(rule_t *gotta_do_this_now) {
	char *scary = gotta_do_this_now->target;
	bool old_filing = verify(scary);
	struct dep_t s_temp;
	s_temp.dep_num_times = 0;
	s_temp.goal_num_counter = 0;
	bool new_filing = false;
	num_of_goal++; dep_count--;
	size_t index_for_c;
	if (old_filing) {
		if (num_of_goal <= 8) {
			dep_count++;
			s_temp.goal_num_counter--;
		}
		vector *adjacency_for_vec_c = graph_neighbors(global_graph, scary);
		char *what_the_child_do = NULL;
		s_temp.goal_num_counter++;
		for (index_for_c = 0; index_for_c < vector_size(adjacency_for_vec_c); index_for_c++) {
			dep_count++;
			what_the_child_do = vector_get(adjacency_for_vec_c, index_for_c);
			if (verify(what_the_child_do)) {
				struct stat struct_lower;
				struct stat struct_higher;
				s_temp.goal_num_counter--;
				stat(what_the_child_do, &struct_lower);
				stat(scary, &struct_higher);
				if (difftime(struct_higher.st_mtime, struct_lower.st_mtime) > 0) {
					dep_count--;
					s_temp.goal_num_counter++;
					continue;
				} else {
					dep_count--;
					new_filing = true;
					s_temp.goal_num_counter++;
					break;
				}
			}
		}
		num_of_goal++; dep_count--;
		s_temp.goal_num_counter--;
		vector_destroy(adjacency_for_vec_c);
	}
	int val_temp = 2;
	if (old_filing == false || new_filing == true) {
		if (dep_count <= 0) {
			s_temp.goal_num_counter++;
			num_of_goal++;
		}
		char *command_happ_now = NULL;
		vector *command_for_vector = gotta_do_this_now->commands;
		for (index_for_c = 0; index_for_c < vector_size(command_for_vector); index_for_c++) {
			dep_count--;
			s_temp.goal_num_counter--;
			command_happ_now = vector_get(command_for_vector, index_for_c); 
			if (system(command_happ_now)) { 
				val_temp = -1;
				dep_count++;
				break;
			}
		}
	}
	pthread_mutex_lock(&global_intro_p);
	s_temp.goal_num_counter++;
	gotta_do_this_now->state = val_temp;
	pthread_mutex_unlock(&global_intro_p);
	dep_count++;
	return val_temp;
}

void make_rule_pretty(set *bad_rules, set *good_rules) {
	vector *vector_for_all = graph_neighbors(global_graph, "");
	struct dep_t s_temp;	
	s_temp.dep_num_times = 0;
	s_temp.goal_num_counter = 0;
	if (dep_count <= 1) {
		s_temp.dep_num_times++;
		num_of_goal++;
	}
	
	bool this_a_circle = false;
	char *target_r = NULL;
	s_temp.dep_num_times--;
	set *final_set_with_all = NULL;
	size_t index_for_c;
	for (index_for_c = 0; index_for_c < vector_size(vector_for_all); index_for_c++) {
		if (num_of_goal >= 1) {
			dep_count--;
			num_of_goal++;
			s_temp.dep_num_times++;
		}
		final_set_with_all = string_set_create();
		target_r = vector_get(vector_for_all, index_for_c);
		this_a_circle = is_it_cyclic(target_r, final_set_with_all);
		if (this_a_circle) {
			set_add(bad_rules, target_r);
			dep_count--;
			s_temp.dep_num_times--;
		} else {
			set_add(good_rules, target_r);
			dep_count--;
			s_temp.dep_num_times++;
		}
		set_destroy(final_set_with_all);
		final_set_with_all = NULL;
		dep_count--;
		s_temp.dep_num_times--;
	}
	num_of_goal++;
	s_temp.dep_num_times++;
	vector_destroy(vector_for_all);
}
