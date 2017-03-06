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
  

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc(n)))"

lemma "ev(Suc(Suc 0))"
  apply(rule evSS)
  apply(rule ev0)
  done

theorem "(isValidPO (transitive_closure (partial_order jctc6)))"
  apply(auto)
  apply(auto simp add:EventStructures.refl_def)
  apply(auto simp add:EventStructures.trans_def)
  apply(auto simp add:EventStructures.antisym_def)
  apply(rule transitive_closure.refl)
  apply(rule transitive_closure.step)
  apply(auto simp add:EventStructures.transitive_closure.step)
  apply(auto simp add:partial_order_def)
  

    
theorem "isValidES jctc6"
apply(auto simp add:isValidES_def)
apply(auto simp add:symmetric_def)
apply(auto simp add:EventStructures.trans_def)
apply(auto simp add:EventStructures.refl_def)
apply(auto simp add:EventStructures.antisym_def)


theorem "\<forall> exp \<in> jctc6_expected_results .
  \<exists> cand_Config . (exp \<subseteq> cand_Config) \<and> (well_justified jctc6 cand_Config)"
sorry
