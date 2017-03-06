theory jctc6
imports EventStructures String
begin

definition jctc6 :: "string event_structure_data" where
"jctc6 \<equiv> \<lparr> 
    event_set = { ''a'', ''b'', ''c'', ''d'', ''e'', ''f'', ''g'', ''h'' },
    partial_order =  \<lambda>x y. (x,y) \<in> { (''a'', ''g''), (''a'', ''e''), (''a'', ''d''), (''a'', ''b''), (''g'', ''h''), (''b'', ''c''), (''e'', ''f'') },
    primitive_conflict =  \<lambda>x y. (x,y) \<in> { (''e'', ''g''), (''b'', ''d'') },
    label_function = \<lambda>x.
        if x = ''b'' then Label R ''A'' 1 (* r1 *)
        else if x = ''c'' then Label W ''B'' 1
        else if x = ''d'' then Label R ''A'' 0 (* r1 *)
        else if x = ''e'' then Label R ''B'' 1 (* r2 *)
        else if x = ''f'' then Label W ''A'' 1
        else if x = ''g'' then Label R ''B'' 0 (* r2 *)
        else if x = ''h'' then Label W ''A'' 1
        else Label I '''' 0
\<rparr>"

definition jctc6_expected_results :: "string set set" where 
"jctc6_expected_results = { {''b'', ''e''} }"

value "\<forall> V \<in> event_set jctc6 . 
  \<exists> e \<in>event_set jctc6 . justifies_event (label_function jctc6 e) (label_function jctc6 V)"
    
theorem "\<not> (isValidPO (partial_order jctc6))"
  apply(auto)
  apply(auto simp add:EventStructures.refl_def)
  apply(auto simp add:jctc6_def)
  done

theorem "(isValidPO (transitive_closure (partial_order jctc6)))"
  apply(auto)
  apply(auto simp add:EventStructures.refl_def)
    apply(rule EventStructures.transitive_closure.intros(1))
   apply(auto simp add: EventStructures.trans_def)
   apply(rule transitive_closure_t)
    apply(simp)
    
   apply(auto simp add:EventStructures.antisym_def)
  apply(simp add: jctc6_def)
    
    try
          
        
        (*
  apply(auto simp add:EventStructures.refl_def)
    apply(auto simp add:EventStructures.trans_def)
    apply(auto simp add:EventStructures.antisym_def)
    apply(rule transitive_closure.cases)
      apply(rule refl)
     apply(rule refl)
    apply(rule refl)
   apply(simp add:transitive_closure.step)
    
  apply(simp)
  apply(auto)
  *)
theorem "isValidES jctc6"
apply(auto simp add:isValidES_def)
apply(auto simp add:symmetric_def)
apply(auto simp add:EventStructures.trans_def)
apply(auto simp add:EventStructures.refl_def)
apply(auto simp add:EventStructures.antisym_def)


theorem "\<forall> exp \<in> jctc6_expected_results .
  \<exists> cand_Config . (exp \<subseteq> cand_Config) \<and> (well_justified jctc6 cand_Config)"
sorry
