theory ExampleEventStructures
imports EventStructures
begin

theorem "well_justified empty_ES"
apply (auto simp add: well_justified_def justified_def empty_ES_def)
apply (rule refl)
done


theorem "well_justified ex1"
apply(auto simp add: well_justified_def)
apply(auto simp add: justified_def)
apply(auto simp add: empty_ES_def)
apply(case_tac r)
apply(auto simp add: "getMemAction.cases")
apply(auto simp add: label_function_def)

apply(auto simp add: ex1_def)



apply(auto simp add: label_function_def)
apply(case_tac )
apply(case_tac getMemAction_cases)
oops

(*Java Causality Test Case 4 Event Structure
  Should NOT be accepted by model*)
definition jctc4_ES :: "nat event_structure_data" where
"jctc4_ES \<equiv> \<lparr> 
  event_set = {0, 1, 2, 3, 4, 5, 6, 7, 8},
  partial_order = \<lambda>x y. (x,y) \<in>
    {(0,1), (0,2), (0, 3), (0, 4), (1,5), (2,6), (3,7), (4,8)},
  primitive_conflict = \<lambda>x y. (y,x) \<in> {(1,2), (3,4)},
  label_function = \<lambda>x.
    if x = 0 then Label I '''' 0
    else if x = 1 then Label R ''x'' 0
    else if x = 2 then Label R ''x'' 1
    else if x = 3 then Label R ''y'' 0
    else if x = 4 then Label R ''y'' 1
    else if x = 5 then Label W ''y'' 1
    else if x = 6 then Label W ''y'' 1
    else if x = 7 then Label W ''x'' 0
    else Label W ''x'' 1
\<rparr>"

(*Java Causality Test Case 6 Event Structure
  Should be accepted by model*)
definition jctc6_ES :: "nat event_structure_data" where
"jctc6_ES \<equiv> \<lparr> 
  event_set = {0, 1, 2, 3, 4, 5, 6, 7},
  partial_order = \<lambda>x y. (x,y) \<in>
    {(0,1), (0,2), (0, 3), (0, 34), (2,5), (3,6), (4,7)},
  primitive_conflict = \<lambda>x y. (y,x) \<in> {(1,2), (3,4)},
  label_function = \<lambda>x.
    if x = 0 then Label I '''' 0
    else if x = 1 then Label R ''x'' 0
    else if x = 2 then Label R ''x'' 1
    else if x = 3 then Label R ''y'' 0
    else if x = 4 then Label R ''y'' 1
    else if x = 5 then Label W ''y'' 1
    else if x = 6 then Label W ''x'' 0
    else Label W ''x'' 1
\<rparr>"
value"''''"
value"label_function jctc6_ES 0"
value"justifies_event (label_function jctc6_ES 5) (label_function jctc6_ES 4)"
value"\<forall>v \<in> {0,1,2,3,4,5,6,7}.\<exists>e\<in>event_set jctc6_ES. justifies_event (label_function jctc6_ES e) (label_function jctc6_ES v)"

theorem "well_justified jctc6_ES"
apply(auto simp add: well_justified_def)
apply(auto simp add: justified_def)
apply(auto simp add: jctc6_ES_def)
apply(rule transitive_closurep_trans' empty_ES_def)

end