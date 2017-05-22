theory jctc4
  imports EventStructures ExampleEventStructures 
          String Relation Transitive_Closure jctc6 ESProperties EventStructures2
begin

definition event_set :: "nat set" where
  "event_set \<equiv> {1, 2, 3, 4, 5, 6, 7, 8, 9}"
  
definition order :: "nat rel" where
  "order \<equiv> { (6, 7), (1, 9), (1, 8), (1, 7), (1, 6), (1, 5), (1, 4), 
            (1, 3), (1, 2), (8, 9), (2, 3), (4, 5) } \<union> Id"

definition primitive_conflict :: "nat rel" where
  "primitive_conflict \<equiv> { (6, 8), (8, 6), (2, 4), (4, 2) }"

definition conflict :: "nat rel" where
  "conflict \<equiv> { (5, 3), (5, 2), (4, 3), (4, 2), (2, 4), (2, 5), (3, 4), (3, 5), (9, 7), (9, 6), (8, 7), (8, 6), (6, 8), (6, 9), (7, 8), (7, 9) }"

interpretation jctc4: labelledES 
  "order"  -- Order
  "event_set" -- Events
  "conflict" -- Conflict
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
      apply(simp only: order_def refl_reflcl)
  apply(simp add: antisym_def order_def)
  apply(simp only: order_def)
     apply(rule trans_reflclI)
     apply(simp add: trans_def)
    apply(simp add: sym_def conflict_def)
   apply(simp add: order_def conflict_def)
  apply (smt num.inject(1) numeral_1_eq_Suc_0 numeral_eq_iff semiring_norm(85) semiring_norm(86) semiring_norm(89) semiring_norm(90))
  done

definition jctc4_expected_results :: "nat set set" where 
"jctc4_expected_results = { {} }"

definition jctc4_forbidden_results :: "nat set set" where 
"jctc4_forbidden_results = { {2, 6} }"

definition jctc4_goal :: "nat set" where
"jctc4_goal \<equiv> {1, 2, 3, 6, 7}"

definition blocking_config :: "nat set" where
"blocking_config \<equiv> {1, 4, 5, 8, 9}"

definition jctc4_goal_events :: "nat set" where
"jctc4_goal_events \<equiv> {2, 3, 6, 7}"

thm spec

lemma empty_init_just : "jctc4.justifies_config_star {} {1}"
  apply(simp add: jctc4.justifies_config_star_def)
    apply(rule r_into_rtranclp)
    apply(simp add: jctc4.justifies_config_subset_def)
    apply(simp add: jctc4.justifies_config_def)
    apply(simp add: jctc4.is_read_def)
done

lemma init_just_blocking : "jctc4.justifies_config_star {1} blocking_config"
  apply(simp add: jctc4.justifies_config_star_def)
    apply(rule r_into_rtranclp)
    apply(simp add: jctc4.justifies_config_subset_def)
    apply(rule conjI)
    apply(simp_all add: blocking_config_def)
    apply(simp add: jctc4.justifies_config_def)
    apply(simp add: jctc4.is_read_def)
done

lemma unfold_trans : "jctc4.justifies_config_star A B \<Longrightarrow> jctc4.justifies_config_star B C \<Longrightarrow> jctc4.justifies_config_star A C"
 apply(simp add: jctc4.justifies_config_star_def jctc4.justifies_config_def)
done

lemma empty_set_just_star_blocking : "jctc4.justifies_config_star {} blocking_config"
  apply(rule unfold_trans[where B="{1}"])
  apply(rule empty_init_just)
  apply(rule init_just_blocking)
done

lemma no_progress_from_blocking : "jctc4.justifies_config_star blocking_config C \<Longrightarrow> (\<forall>e\<in>jctc4_goal_events. jctc4.is_read e \<Longrightarrow> e \<notin> C)"
  apply(simp add: jctc4.justifies_config_star_def blocking_config_def jctc4_goal_events_def)
  apply(simp add: jctc4.justifies_config_def jctc4.is_read_def)
done

lemma blocking_is_maximal : "jctc4.is_maximal jctc4.event_set jctc4.blocking_config"
  apply(simp add: jctc4.is_maximal_def)
  apply(simp add: blocking_config_def event_set_def)
  done

lemma no_more_events_in_maximal_configs : "\<forall>C\<in>jctc4.config_domain. jctc4.is_maximal jctc4.event_set C \<Longrightarrow> \<not>(\<exists>e\<in>jctc4.event_set. (C \<union> {e}) \<in> jctc4.config_domain)"
  apply(simp add: jctc4.is_maximal_def)
  nitpick

lemma "\<forall>C\<in>jctc4.config_domain. \<forall>C'\<in>jctc4.config_domain. jctc4.is_maximal jctc4.event_set C 
  \<Longrightarrow> jctc4.justifies_config_star C C' \<Longrightarrow> C = C'"
  apply(rule)
  apply (simp add: jctc4.justifies_config_star_def jctc4.justifies_config_subset_star_subset) 
  apply(simp add: jctc4.is_maximal_def jctc4.justifies_config_star_def)
  apply(rule ccontr)
sorry
  
lemma blocking_just_self_only : "jctc4.justifies_config_star blocking_config C \<Longrightarrow> C = blocking_config"
  apply(simp add: jctc4.justifies_config_star_def)
  apply(rule rtranclp_induct[where r=jctc4.justifies_config_subset, where ?a=C])
  (*apply(frule jctc4.justifies_config_subset_star_subset)*)
  sorry
 
lemma blocking_config_valid : "blocking_config \<in> jctc4.config_domain"
  apply(simp add: jctc4.config_domain_def)
  apply(simp add: jctc4.down_closed_def jctc4.conflict_free_def)
  apply(simp add: blocking_config_def order_def conflict_def)
  apply(auto)
done


lemma "jctc4.ae_justifies_subset {} C \<Longrightarrow> \<not>(jctc4_goal_events \<subseteq> C)"
    apply(simp add: jctc4.ae_justifies_subset_def jctc4.ae_justifies_def)
    apply(frule bspec[where A=jctc4.config_domain, where x="blocking_config"])
    apply(simp add: blocking_config_valid)
    apply(rule)
    
    (*apply()
    apply(simp add: blocking_just_self_only)*)
    

lemma crux : "jctc4.ae_justifies_subset x y \<Longrightarrow> (\<forall>e\<in>jctc4_goal_events. e \<notin> x) \<Longrightarrow> (\<forall>e\<in>jctc4_goal_events. e \<notin> y)"
    apply(simp add: jctc4.ae_justifies_subset_def jctc4.ae_justifies_def)
    apply(clarsimp)
    

(*apply(frule spec[where x=blocking_config])*)
sorry

lemma events_not_in_goal : "(\<forall>e \<in>jctc4_goal_events. e \<notin> B)  \<Longrightarrow> B \<noteq> jctc4_goal"
apply(simp add: jctc4_goal_def jctc4_goal_events_def)
apply(auto)
done

thm rtrancl_induct[where a="{}", where b=C, where r="{(c\<^sub>1, c\<^sub>2). jctc4.ae_justifies_subset c\<^sub>1 c\<^sub>2}"]

lemma never_jctc4_goal: "jctc4.well_justified C \<Longrightarrow> C \<noteq> jctc4_goal"
  apply(unfold jctc4.well_justified_def)
  apply(rule events_not_in_goal)
  apply(rule rtranclp_induct[where a="{}", where b=C, where r="jctc4.ae_justifies_subset", 
      where P="\<lambda>x. (\<forall>e \<in>jctc4_goal_events. e \<notin> x)"])
  apply(clarify)
  apply(simp add: jctc4.ae_justifies_subset_star_def)
  apply(simp)
  
sorry
(*  
  
  apply(assumption)
  apply(simp)*)

theorem "\<not>(jctc4.well_justified jctc4_goal)"
  apply(rule ccontr)
  apply(simp add: never_jctc4_goal)
    apply(frule never_jctc4_goal)
    apply(simp)
    done


(**


value "\<forall> V \<in> event_set jctc4 . 
  \<exists> e \<in>event_set jctc4 . justifies_event (label_function jctc4 e) (label_function jctc4 V)"

theorem "\<forall> exp \<in> jctc4_expected_results .
  \<exists> cand_Config . (exp \<subseteq> cand_Config) \<and> (well_justified jctc6 cand_Config)"
sorry



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

lemma init_just_blocking : "{1} \<lesssim>\<^bsub>jctc4\<^esub> blocking_config"
  apply(simp add: justifies_config_inf_def)
  apply(simp add: justifies_config_subset_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  apply(auto simp add: blocking_config_def)
  apply(simp add: is_read_def jctc4_def)+
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






thm spec[where x=blocking_config]




**)

end