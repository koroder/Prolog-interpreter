Control.Print.printDepth := 100;

CM.make "sources.cm";

open Absyn

	
(*2*)
(*2.c apply substitution rho to term t*)
fun	 rho_val (vart,[]) = Node("VARIABLE",[Leaf(vart)])
	|rho_val (vart,((a,b)::tl)) = if(vart = a) then b else rho_val(vart,tl);
	
fun	 subst (Null,rho) = Null	
	|subst (Node("VARIABLE",[Leaf(x)]),rho) = rho_val(x,rho) (*this wrong variable may be mapped to functions--correct *)
	|subst (Node("NAME",[Leaf(x)]),rho) = Node("NAME",[Leaf(x)])
	|subst (Node(x,y),rho) = Node(x,subst_ls(y,rho))
and
	 subst_ls ([],rho) = []
	|subst_ls (hd::tl,rho) = [subst(hd,rho)] @ subst_ls(tl,rho);
	
(*2.b composition of substituion*)

fun	 exist_rho1 ([],hd) = false
	|exist_rho1 ((a,Node(b,c))::tl,(p,Node(q,r))) = (p=a) orelse exist_rho1(tl,(p,Node(q,r)));
	
fun	 left_rho2 (r1,[]) = []
	|left_rho2 (r1,(hd::tl)) = if(exist_rho1(r1,hd)) then left_rho2(r1,tl)
				   else [hd] @ left_rho2(r1,tl); 
	
fun	 compose_subst ((x,Node(a,b))::tl,r2) = if (tl=[]) then [(x,subst(Node(a,b),r2))]
						else [(x,subst(Node(a,b),r2))] @ compose_subst(tl,r2);	
	
fun	 compose ([],[]) = [] 
	|compose (r1,[]) = r1
	|compose ([],r2) = r2
	|compose (r1,r2) = compose_subst(r1,r2) @ left_rho2(r1,r2);
	
(*most general unifier*)

exception MGU_FAIL;

(*to check if variable of one expression is in other*)
fun	 isInVars([],x) = false
	|isInVars(hd::tl,x) = (hd = x) orelse isInVars(tl,x);
	
(*to find variables in an expression*)
fun	 vars(Node("VARIABLE",[Leaf(x)])) = [x]
	|vars(Node("NAME",y)) = []
	|vars(Node(x,y)) = vars_ls(y)
and
	 vars_ls([]) = []
	|vars_ls(hd::tl) = vars(hd) @ vars_ls(tl);

(*unifier*)
fun	unif (Node(x,[Leaf(x1)]),Node(y,[Leaf(y1)]),var_list1,var_list2) = if(x1=y1) then []
					 				   else if(x="VARIABLE" andalso y="VARIABLE") then [(x1,Node(y,[Leaf(y1)]))]
					 				   else if(x="VARIABLE" andalso y<>"VARIABLE") then [(x1,Node(y,[Leaf(y1)]))]
					 				   else if(x<>"VARIABLE" andalso y="VARIABLE") then [(y1,Node(x,[Leaf(x1)]))]
					 				   else raise MGU_FAIL
	|unif (Node(x,[Leaf(x1)]),Node(a,b),var_list1,var_list2) = if(x<>"VARIABLE") then raise MGU_FAIL
								   else if(isInVars(var_list2,x1)) then raise MGU_FAIL
								   else [(x1,Node(a,b))]
	|unif (Node(a,b),Node(x,[Leaf(x1)]),var_list1,var_list2) = if(x<>"VARIABLE") then raise MGU_FAIL
							           else if(isInVars(var_list1,x1)) then raise MGU_FAIL
							           else [(x1,Node(a,b))]
	|unif (Node(a,b),Node(x,y),var_list1,var_list2) = if(length(b) <> length(y)) then raise MGU_FAIL
							  else temp(b,y,[],var_list1,var_list2)
and
	 temp([],[],rho_eff,var_list1,var_list2) = rho_eff
	|temp(hd1::l1,hd2::l2,rho_eff,var_list1,var_list2) = temp(l1,l2,compose(rho_eff,unif(subst(hd1,rho_eff),subst(hd2,rho_eff),var_list1,var_list2)), 																		      var_list1,var_list2);
(*mgu will return tuple--(unifier,unifiable)*)
fun	mgu (Node(x,y),Node(a,b)) = (unif(Node(x,y),Node(a,b),vars(Node(x,y)),vars(Node(a,b))),true) handle MGU_FAIL => ([],false);

(*solve and resolution*)

(* taking out proper tree from our defined tree. This will help in obtaining mgu *)
fun	 proper_tree_rule(Node("BEGIN",hd::tl)) = proper_tree_rule(hd)
	|proper_tree_rule(Node("PROGRAM",hd::tl)) = proper_tree_rule(hd) @ proper_tree_rule_ls(tl)
	|proper_tree_rule(Node("STATEMENT",hd::tl)) = proper_tree_rule(hd)
	|proper_tree_rule(Node("FACT",l)) = l
	|proper_tree_rule(Node("RULE",hd::tl)) = proper_tree_rule(hd) @ proper_tree_rule_ls(tl)
	|proper_tree_rule(Node("HEAD",l)) = l
	|proper_tree_rule(Node("BODY",hd::tl)) = [hd] @ proper_tree_rule_ls(tl)
and
	 proper_tree_rule_ls([]) = []
	|proper_tree_rule_ls(hd::tl) = proper_tree_rule(hd) @ proper_tree_rule_ls(tl); 

fun	 proper_tree(Node("BEGIN",hd::tl)) = proper_tree(hd)
	|proper_tree(Node("PROGRAM",hd::tl)) = proper_tree(hd) @ proper_tree_ls(tl)
	|proper_tree(Node("STATEMENT",hd::tl)) = proper_tree(hd)
	|proper_tree(Node("FACT",l)) = [l]
	|proper_tree(Node("RULE",hd::tl)) = [proper_tree_rule(Node("RULE",hd::tl))]
and
	 proper_tree_ls([]) = []
	|proper_tree_ls(hd::tl) = proper_tree(hd) @ proper_tree_ls(tl); 

(*convert goal list list into goal list*)	
fun	 goal_list([]) = []
	|goal_list(hd::tl) = hd @ goal_list(tl);

(*solve and resolution*)

(*perform substitution on query*)
fun	 subst_query([],rho) = []
	|subst_query(hd::tl,rho) = [subst(hd,rho)] @ subst_query(tl,rho);

(*concatenate tl of clause with tl of goal and perform substitution using mgu of hd(clause) and hd(goal)*)
fun	resolution_goal_new(hd_c::tl_c,hd_g::tl_g) = resolution_goal_new_ls((tl_c @ tl_g),#1(mgu(hd_c,hd_g)))
and	 
	 resolution_goal_new_ls([],rho) = []
	|resolution_goal_new_ls(hd::tl,rho) =  [subst(hd,rho)] @ resolution_goal_new_ls(tl,rho);

fun	resolution(hd_clause::tl_clause,hd_goal::tl_goal,query) = 
 		(resolution_goal_new(hd_clause::tl_clause,hd_goal::tl_goal),subst_query(query,#1(mgu(hd_clause,hd_goal))));

(*rename variables--append number to variables only*)
fun	 rename_h(Node ("VARIABLE",[Leaf(v)]),n) = Node ("VARIABLE",[Leaf(v ^ Int.toString(n))])
	|rename_h(Node("NAME",l),n) = Node("NAME",l)
	|rename_h(Node(x,hd::tl),n) = Node(x,[rename_h(hd,n)] @ rename_h_ls(tl,n)) 
and
	 rename_h_ls([],n) = []
	|rename_h_ls(hd::tl,n) = [rename_h(hd,n)] @ rename_h_ls(tl,n);
 		
fun	 rename([],n) = []
	|rename(hd::tl,n) = [rename_h(hd,n)] @ rename(tl,n);

(*solve given-goals,clause, and return answer--query*)
fun	 solve([],query,clause,clause1,n) = query
	|solve(goal,query,[],clause1,n) = []
	|solve(goal,query,hd_c::tl_c,clause1,n) = if(#2(mgu(hd(rename(hd_c,n)),hd(goal)))) then solve(#1(resolution(rename(hd_c,n),goal,query)),#2(resolution(rename(hd_c,n),goal,query)),clause1,clause1,n+1) @ solve(goal,query,tl_c,clause1,n)
						 else solve(goal,query,tl_c,clause1,n);

(*final answer*)
(*answer is a list of facts involving only names*)
fun answer_final(term1,term2) = solve(goal_list(proper_tree(term2)),goal_list(proper_tree(term2)),proper_tree(term1),proper_tree(term1),0);
print("GIVE IN THE QUERY: \n");
val answer = answer_final(Parse.file_parse "input.txt", Parse.query_parse((TextIO.input(TextIO.stdIn))));





	


