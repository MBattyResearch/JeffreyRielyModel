theory jctc4
  imports EventStructures ExampleEventStructures 
          String Relation Transitive_Closure jctc6 ESProperties EventStructures2
begin

interpretation jctc4: labelledES 
  "{{ (6, 7), (1, 8), (1, 6), (1, 4), (1, 2), (8, 9), (2, 3), (4, 5) }*"  -- Order
  "{1, 2, 3, 4, 5, 6, 7, 8, 9}" -- Events
  "(x, y) \<in> { (6, 8), (2, 4) }" -- Conflict
  "\<lambda>x. if x = 2 then Label R ''x'' 1 (* r1 *)
    else if x = 3 then Label W ''y'' 1
    else if x = 4 then Label R ''x'' 0 (* r1 *)
    else if x = 5 then Label W ''y'' 0
    else if x = 6 then Label R ''y'' 1 (* r2 *)
    else if x = 7 then Label W ''x'' 1
    else if x = 8 then Label R ''y'' 0 (* r2 *)
    else if x = 9 then Label W ''x'' 0
    else Label I '''' 0" -- Labelling

  apply(unfold_locales) 
  apply(auto)
   apply (metis Domain_empty Domain_insert Not_Domain_rtrancl singleton_iff)
  done



(**
definition jctc4 :: "nat event_structure" where
"jctc4 \<equiv> \<lparr> 
    event_set = { 1, 2, 3, 4, 5, 6, 7, 8, 9 },
    primitive_order = { (6, 7), (1, 8), (1, 6), (1, 4), (1, 2), (8, 9), (2, 3), (4, 5) },
    primitive_conflict =  { (6, 8), (2, 4) },
    label_function = \<lambda>x.
        if x = 2 then Label R ''x'' 1 (* r1 *)
        else if x = 3 then Label W ''y'' 1
        else if x = 4 then Label R ''x'' 0 (* r1 *)
        else if x = 5 then Label W ''y'' 0
        else if x = 6 then Label R ''y'' 1 (* r2 *)
        else if x = 7 then Label W ''x'' 1
        else if x = 8 then Label R ''y'' 0 (* r2 *)
        else if x = 9 then Label W ''x'' 0
        else Label I '''' 0
\<rparr>"

definition order :: "nat rel" where
"order \<equiv> { (6, 7), (6, 6), (3, 3), (1, 9), (1, 8), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (1, 1), (8, 9), (8, 8), (7, 7), (2, 3), (2, 2), (9, 9), (4, 5), (4, 4), (5, 5) }"

definition constructed_pc :: "nat rel" where
"constructed_pc \<equiv> { (6, 8), (8, 6), (2, 4), (4, 2) }"

definition jctc4_expected_results :: "nat set set" where 
"jctc4_expected_results = { {} }"

definition jctc4_forbidden_results :: "nat set set" where 
"jctc4_forbidden_results = { {2, 6} }"

value "\<forall> V \<in> event_set jctc4 . 
  \<exists> e \<in>event_set jctc4 . justifies_event (label_function jctc4 e) (label_function jctc4 V)"

theorem "\<forall> exp \<in> jctc4_expected_results .
  \<exists> cand_Config . (exp \<subseteq> cand_Config) \<and> (well_justified jctc6 cand_Config)"
sorry

definition jctc4_goal :: "nat set" where
"jctc4_goal \<equiv> {1, 2, 3, 6, 7}"

definition blocking_config :: "nat set" where
"blocking_config \<equiv> {1, 4, 5, 8, 9}"

lemma "blocking_config  \<lesssim>\<^sup>*\<^bsub>jctc4\<^esub> C \<Longrightarrow> 8 \<notin> C \<and> 6 \<notin> C"
  apply(simp add: justifies_config_star_inf_def)
  apply(simp add: justifies_config_subset_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  apply(rule conjI)
  apply(auto)
oops

lemma "({}, blocking_config) \<in> {(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<lesssim>\<^bsub>jctc4\<^esub> c\<^sub>2}"
apply(simp add: ae_justifies_subset_def)
oops

lemma two_step_in_trans : "A \<lesssim>\<^bsub>es\<^esub> B \<Longrightarrow> B \<lesssim>\<^bsub>es\<^esub> C \<Longrightarrow> A  \<lesssim>\<^sup>*\<^bsub>es\<^esub> C"
 apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
done

lemma empty_init_just : "{}  \<lesssim>\<^bsub>jctc4\<^esub> {1}"
  apply(simp add: justifies_config_inf_def)
  apply(simp add: justifies_config_subset_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  apply(simp add: is_read_def jctc4_def)
done

lemma foo :"C \<subseteq> blocking_config \<Longrightarrow> C \<union> {1} \<lesssim>\<^bsub>jctc4\<^esub> blocking_config"
  apply(simp add: justifies_config_inf_def)
  apply(simp add: justifies_config_subset_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  apply(auto simp add: blocking_config_def)
  apply(simp add: is_read_def jctc4_def)+
done



thm bexI  
  
lemma init_just_blocking : "{1} \<lesssim>\<^bsub>jctc4\<^esub> blocking_config"
  apply(simp add: justifies_config_inf_def)
  apply(simp add: justifies_config_subset_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  apply(auto simp add: blocking_config_def)
  apply(simp add: is_read_def jctc4_def)+
  done

lemma empty_set_just_star_blocking : "{} \<lesssim>\<^sup>*\<^bsub>jctc4\<^esub> blocking_config"
  apply(rule two_step_in_trans[where B="{1}"])
  apply(rule empty_init_just)
  apply(rule init_just_blocking)
done

lemma blocking_conf_term : "blocking_config \<lesssim>\<^sup>*\<^bsub>jctc4\<^esub> C \<Longrightarrow> blocking_config = C"
sorry

lemma "\<not>(blocking_config \<lesssim>\<^sup>*\<^bsub>jctc4\<^esub> jctc4_goal)"
  apply(insert blocking_conf_term)
  apply(simop add: )
  apply(simp add: justifies_config_star_inf_def)
  apply(simp add: justifies_config_subset_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  


 sorry

thm rtrancl_induct[where a="{}", where b=B, where r="{(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<sqsubseteq>\<^bsub>jctc4\<^esub> c\<^sub>2}", where P="\<lambda>x. 2 \<notin> x \<and> 3 \<notin> x \<and> 6 \<notin> x \<and> 7 \<notin> x"]

lemma events_not_in_goal : "2 \<notin> B \<and> 3 \<notin> B \<and> 6 \<notin> B \<and> 7 \<notin> B \<and> x \<subseteq> (event_set jctc4) \<Longrightarrow> B \<noteq> jctc4_goal"
apply(simp add: jctc4_goal_def)
apply(auto)
done

lemma expand_justifies_config_star :"C \<lesssim>\<^sup>*\<^bsub>es\<^esub> D \<Longrightarrow> D \<lesssim>\<^sup>*\<^bsub>es\<^esub> E \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> E"
apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
done

lemma expand_justifies_config_star_R :"C \<lesssim>\<^bsub>es\<^esub> D \<Longrightarrow> D \<lesssim>\<^sup>*\<^bsub>es\<^esub> E \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> E"
apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
done

lemma expand_justifies_config_star_L :"C \<lesssim>\<^sup>*\<^bsub>es\<^esub> D \<Longrightarrow> D \<lesssim>\<^bsub>es\<^esub> E \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> E"
apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
done

lemma "y \<subseteq> blocking_config \<Longrightarrow>  y \<lesssim>\<^sup>*\<^bsub>jctc4\<^esub> blocking_config"
apply(case_tac "y={}")
apply(simp add: empty_set_just_star_blocking)
apply(rule expand_justifies_config_star[where D="y \<union> {1}"])
apply(rule expand_justifies_config_star_R[where D="y"])
defer
apply(rule add_write_really_okay)
sorry

thm add_write_really_okay
thm add_write_okay
thm expand_justifies_config_star

apply(simp add: justifies_config_star_inf_def justifies_config_subset_def)
  apply(simp add: justifies_config_def)
apply(simp add: is_read_def)


thm foo

lemma events_imply_subset : "2 \<notin> y \<Longrightarrow> 3 \<notin> y \<Longrightarrow> 6 \<notin> y \<Longrightarrow> 7 \<notin> y \<Longrightarrow>
    y \<subseteq> event_set jctc4 \<Longrightarrow> y \<subseteq> blocking_config"
apply(simp add: blocking_config_def jctc4_def)
apply(auto)
done

lemma "y \<noteq> {} \<Longrightarrow> y \<subseteq> blocking_config \<Longrightarrow> y \<lesssim>\<^bsub>jctc4\<^esub> y \<union> {1}"
  apply(simp only: justifies_config_inf_def justifies_config_subset_def justifies_config_def)
  apply(simp add: blocking_config_def jctc4_def is_read_def)
apply(rule conjI)
apply(clarsimp)



lemma "1 = Suc 0"

lemma "2 \<notin> y \<Longrightarrow> 3 \<notin> y \<Longrightarrow> 6 \<notin> y \<Longrightarrow> 7 \<notin> y \<Longrightarrow>
    y \<subseteq> event_set jctc4 \<Longrightarrow> y \<lesssim>\<^sup>*\<^bsub>jctc4\<^esub> blocking_config"
apply(rule expand_justifies_config_star_R[where D="y \<union> {1}"])
defer
apply(frule events_imply_subset)
apply(simp)
apply(simp)
apply(simp)
apply(simp)
apply(rule just_star_imp_just)
apply(rule foo)
apply(assumption)
apply(case_tac "y={}")
apply(simp del: Nat.One_nat_def)
apply(rule empty_init_just)


apply(frule events_imply_subset)
apply(simp)
apply(simp)
apply(simp)
apply(simp)



lemma crux : "(y, z) \<in> {(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<sqsubseteq>\<^bsub>jctc4\<^esub> c\<^sub>2} \<Longrightarrow> 2 \<notin> y \<and> 3 \<notin> y \<and> 6 \<notin> y \<and> 7 \<notin> y \<and> y \<subseteq> event_set jctc4 \<Longrightarrow> 2 \<notin> z \<and> 3 \<notin> z \<and> 6 \<notin> z \<and> 7 \<notin> z \<and> z \<subseteq> event_set jctc4"
apply(simp add: ae_justifies_subset_def ae_justifies_def)
apply(clarsimp)
apply(frule spec[where x=blocking_config])



thm spec[where x=blocking_config]


lemma never_jctc4_goal: "{} \<sqsubseteq>\<^sup>*\<^bsub>jctc4\<^esub> B \<Longrightarrow> B \<noteq> jctc4_goal"
apply(simp add: ae_justifies_subset_star_def)
apply(rule events_not_in_goal)
apply(rule rtrancl_induct[where a="{}", where b=B, where r="{(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<sqsubseteq>\<^bsub>jctc4\<^esub> c\<^sub>2}", where P="\<lambda>x. 2 \<notin> x \<and> 3 \<notin> x \<and> 6 \<notin> x \<and> 7 \<notin> x \<and> x \<subseteq> (event_set jctc4)"])
apply(assumption)
apply(simp)


lemma "\<not>({} \<sqsubseteq>\<^sup>*\<^bsub>jctc4\<^esub> jctc4_goal)"
  apply(rule ccontr)
 apply(simp add: never_jctc4_goal)  
apply(frule never_jctc4_goal)
apply(simp)
done
  

theorem "\<not>(well_justified jctc4 jctc4_goal)"
  apply(simp add: well_justified_def)
  apply(simp add: isValidES_def)
  apply(auto)
  apply(simp add: justified_def)
oops

**)

end