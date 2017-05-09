theory jctc6
  imports EventStructures ESProperties
          String Relation Transitive_Closure 
begin

definition jctc6 :: "nat event_structure" where
"jctc6 \<equiv> \<lparr>
    event_set = { 1, 2, 3, 4, 5, 6, 7, 8 },
    primitive_order = { (1, 7), (1, 5), (1, 4), (1, 2), (7, 8), (2, 3), (5, 6) },
    primitive_conflict =  { (5, 7), (2, 4) },
    label_function = \<lambda>x.
        if x = 2 then Label R ''A'' 1 (* r1 *)
        else if x = 3 then Label W ''B'' 1
        else if x = 4 then Label R ''A'' 0 (* r1 *)
        else if x = 5 then Label R ''B'' 1 (* r2 *)
        else if x = 6 then Label W ''A'' 1
        else if x = 7 then Label R ''B'' 0 (* r2 *)
        else if x = 8 then Label W ''A'' 1
        else Label I '''' 0
\<rparr>"

definition order :: "nat rel" where
"order \<equiv> { (6, 6), (3, 3), (1, 8), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (1, 1), (8, 8), (7, 8), (7, 7), (2, 3), (2, 2), (4, 4), (5, 6), (5, 5) }"

definition constructed_pc :: "nat rel" where
"constructed_pc \<equiv> { (2, 4), (4, 2), (5, 7), (7, 5) }"

definition jctc6_expected_results :: "nat set set" where 
"jctc6_expected_results = { {2, 5} }"

lemma jctc6_acyc_po: "acyclic (primitive_order jctc6)"
  apply(simp add: jctc6_def)
  apply(auto)
        apply(simp add: acyclic_def)
       apply(rule rtrancl.cases, auto)+
  done

lemma jctc6_valid_PO: "isValidPO (event_set jctc6) ((primitive_order jctc6)\<^sup>*)"
  apply(auto simp add: isValidPO_def)
    apply(rule refl_rtrancl)
    apply(rule trans_rtrancl)
  apply(rule acyclic_impl_antisym_rtrancl)
  apply(simp add: jctc6_acyc_po)
  done

lemma jctc6_is_finite: "finite (event_set jctc6)"
  by (simp add: jctc6_def)
  
lemma jctc6_symm_conflict: "sym ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(simp add: sym_def)
  apply (meson symm_pc sym_def)
  done
    
lemma jctc6_is_conf_valid: "isConfValid ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(simp add: isConfValid_def jctc6_symm_conflict trans_rtrancl)
  done
        
lemma rtrancl_subset_po: "((primitive_order jctc6)\<^sup>*) \<subseteq> (order \<union> Id)"
  apply(rule subrelI)
  apply(rule rtrancl.induct [where ?P = "\<lambda>x y. (x,y) \<in> (order  \<union> Id)"])
    apply(simp)
   apply (simp_all add: jctc6_def order_def)
   apply (smt num.inject(1) num.inject(2) numeral_1_eq_Suc_0 numeral_eq_iff semiring_norm(85) semiring_norm(86) semiring_norm(89))
  done
    
lemma order_sub2: "order \<union> Id \<subseteq> ((primitive_order jctc6)\<^sup>*)"
  apply(rule subrelI)
    apply(simp add: order_def jctc6_def)
  apply auto
  apply (meson insertI1 insertI2 r_into_rtrancl rtrancl.rtrancl_into_rtrancl)+
  done
    
lemma order_eq_po_order_trancl: "((primitive_order jctc6)\<^sup>*) = order \<union> Id"
  apply(rule equalityI rtrancl_subset_po order_sub2)+
  done
  
lemma trancl_pc_subset_constructed_pc_id: "((symmetriccl (primitive_conflict jctc6))\<^sup>+) \<subseteq> constructed_pc \<union> Id"
  apply(rule subrelI)
  apply(rule trancl.induct [where ?P = "\<lambda>x y. (x,y) \<in> constructed_pc \<union> Id"])
    apply (simp_all add: jctc6_def constructed_pc_def symmetriccl_def)
  apply(auto)
  done

lemma pc_subset_constructed_pc: "((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id) \<subseteq> constructed_pc"
  apply(rule alg_subset)
  apply(rule trancl_pc_subset_constructed_pc_id)
  done
    
lemma constructed_pc_subset_pc: "constructed_pc \<subseteq> ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(rule subrelI)
    apply(simp add: symmetriccl_def constructed_pc_def jctc6_def)
  apply auto
  done
    
lemma constructed_pc_correct: "((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id) = constructed_pc"
  apply(rule equalityI constructed_pc_subset_pc pc_subset_constructed_pc)+
  done
    
lemma jctc6_is_minimal: "minimal ((primitive_order jctc6)\<^sup>*) ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(simp add: minimal_def constructed_pc_correct order_eq_po_order_trancl)
  apply(simp add: constructed_pc_def order_def)
  apply (smt num.inject(1) num.inject(2) numeral_1_eq_Suc_0 numeral_eq_iff semiring_norm(85) semiring_norm(86) semiring_norm(89))
  done

theorem jctc_isValid: "isValidES jctc6"
  apply(simp add: isValidES_def)
  apply(simp add: jctc6_is_finite)
  apply(simp add: jctc6_valid_PO)
  apply(simp add: jctc6_is_minimal)
  apply(simp add: jctc6_is_conf_valid)
  done

definition jctc6_exec:: "nat set" where
  "jctc6_exec \<equiv> {1,2,3,5,6}"

definition jctc6_C2:: "nat set" where
  "jctc6_C2 \<equiv> {1,2,3}"
  
theorem jctc6_reads: "(getMemAction (label_function jctc6 r) = R) = (r \<in> {4,7,2,5})"
  apply(simp add:jctc6_def)
  done   

lemma not_read_1[simp]: "\<not>(getMemAction (label_function jctc6 (Suc 0)) = R)"
  apply(simp add: jctc6_def)
  done

lemma not_read_3[simp]: "\<not>(getMemAction (label_function jctc6 3) = R)"
  apply(simp add: jctc6_def)
  done
    
lemma is_read_simp[simp]: "\<not>(getMemAction (label_function es x) = R) \<Longrightarrow> (is_read x es = False)"
  apply(simp add: is_read_def)
  done

lemma is_read_2[simp]: "getMemAction (label_function jctc6 2) = R"
  apply(simp add: jctc6_def)
  done
        
lemma not_read_6[simp]: "\<not> (getMemAction (label_function jctc6 6) = R)"
  apply(simp add: jctc6_def)
  done

lemma read_of_init_7[simp]: "(getMemAction (label_function jctc6 7) = R) \<and> 
    justifies_event (label_function jctc6 1) (label_function jctc6 7)"
  apply(simp add: jctc6_def)
  done
    
lemma not_read_8[simp]: "\<not> (getMemAction (label_function jctc6 8) = R)"
  apply(simp add: jctc6_def)
  done
    
lemma write_add_justified: (*"{} \<lesssim>\<^sup>*\<^bsub>es\<^esub> C \<Longrightarrow> 6 \<notin> C' \<and> 8 \<notin> C' \<Longrightarrow> 5 \<in> C \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<union> {6} \<and> (C, C \<union> {6}) \<in> justifies_config jctc6"*)
  "{} \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C' \<Longrightarrow>
          6 \<notin> C' \<and> 8 \<notin> C' \<Longrightarrow>
          5 \<in> C' \<Longrightarrow>
          C' \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> insert 6 C' \<and>
          (insert 6 C', jctc6_C2) \<in> justifies_config jctc6"
  apply (simp add: justifies_config_def)
  apply(rule conjI)
  apply(insert just_star_imp_just [where es=jctc6, where C'=C'])
    apply(simp)
  apply(simp add: justifies_config_star_inf_def justifies_config_subset_def justifies_config_inf_def)
  apply(rule r_into_rtrancl)
  apply(simp)
  apply(rule conjI)
    apply(auto)[1]
  apply (simp add: justifies_config_def is_read_def)
  apply(auto)[1]
  apply (simp add: is_read_def)
  apply(auto simp add: jctc6_def jctc6_C2_def)
  done
    
lemma add_init_justified[simp]: "{} \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<union> {1}"
  apply (simp add: justifies_config_def)
      apply(insert just_star_imp_just)
  apply(simp add: justifies_config_star_inf_def justifies_config_subset_def justifies_config_inf_def)
      apply(rule r_into_rtrancl)
  apply(simp)
  apply(rule conjI)
    apply(auto)[1]
  apply(simp add: justifies_config_def is_read_def)
  done

lemma add_7_8_justified: "{} \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C' \<Longrightarrow> 6 \<notin> C' \<Longrightarrow> 8 \<notin> C' \<Longrightarrow> 5 \<notin> C' \<Longrightarrow>
   (C' \<union> {1, 7, 8}, jctc6_C2) \<in> justifies_config jctc6"
  apply(simp add: justifies_config_star_inf_def justifies_config_subset_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  apply(simp add: jctc6_C2_def jctc6_def)
  done

lemma justified_7_8: "justified jctc6 {1,7,8}"
  apply(simp add: jctc6_def justified_def)
  done

lemma add_1: "{} \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<Longrightarrow> C \<union> {1} \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<union> {1,7,8} \<Longrightarrow> C  \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<union> {1,7,8}"
  apply(insert add_init_justified)
  apply (simp only: justifies_config_star_inf_def)
  by fastforce
    
lemma add_7_8_allowed: "{} \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<Longrightarrow> 6 \<notin> C \<Longrightarrow> 8 \<notin> C \<Longrightarrow> 5 \<notin> C \<Longrightarrow> 
    C \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C \<union> {1, 7, 8}"
  apply(rule add_1)
    apply(assumption)
   apply(insert just_star_imp_just)
  apply(simp only: justifies_config_star_inf_def)
  apply(simp only: justifies_config_subset_def justifies_config_inf_def)
   apply(simp only: justifies_config_def)
  apply(rule r_into_rtrancl)
  apply(auto)[1]
   apply(simp add: jctc6_def)
  done
    
text {* We want to case split on C', if C' contains a write from which we can justify 2 then we're 
good and don't need to add anything to C''. Otherwise we need to add a write like 6 or 8. 
There's no move for C' which doesn't allow adding 6 or 8 to the C'' set. *}
theorem round_1: "({}, jctc6_C2) \<in> {(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<sqsubseteq>\<^bsub>jctc6\<^esub> c\<^sub>2}"
  apply(simp add: ae_justifies_subset_def ae_justifies_def)
  apply (rule allI)
  apply(rule impI)
  apply(case_tac "6 \<in> C' \<or> 8 \<in> C'")
  apply(rule_tac x=C' in exI)
    -- {* We have the cases for C' now. Let's dispatch the first where we don't need to add 
          anything to C''*}
    -- {* When 6 is in C', we can pick C'' = C' and always add 5 to D *}
   apply(simp add: justifies_config_inf_def justifies_config_def)
   apply(simp add: jctc6_reads jctc6_C2_def is_read_def)
   apply(auto)[1]

    -- {* This handles the 6 \<in> C'' case. 6 can justify 2 so we're good to proceed. *}
    apply(rule_tac x=6 in bexI)
     apply(simp add: jctc6_def)
     apply(assumption)
    
    -- {* This handles the 8 \<in> C'' case. 8 can justify 2 so we're good to proceed. *}
    apply(rule_tac x=8 in bexI)
     apply(simp add: jctc6_def)
    apply(assumption)
    
    apply auto[1]
    -- {* This is the 6 in C' case done \o/ *}
    
  -- {* If 5 is in C' we may add 6 *}
  apply(case_tac "5 \<in> C'")
   apply(rule_tac x="C'\<union>{6}" in exI)
   apply(simp add: write_add_justified)
    
  -- {* If 5 is not in C' we can add 7 and 8 as they're not in conflict. This gets us towards our 
        goal. Adding 7 is justified by the init, and adding 8 is justified because 8 is a write. *}
  apply(rule_tac x="C'\<union>{1,7,8}" in exI)
  apply(rule conjI)
   apply(rule add_7_8_allowed, assumption+)
  apply(rule add_7_8_justified, assumption+)
  done
    

lemma C2_subset_exec: "jctc6_C2 \<subseteq> jctc6_exec"
  apply(auto simp add: jctc6_C2_def jctc6_exec_def)  
  done

lemma "{1,2,3} \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> jctc6_exec \<Longrightarrow> {1,2,3} \<union> m \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> jctc6_exec"
  apply(simp only: justifies_config_star_inf_def)
  apply(simp only: justifies_config_subset_def justifies_config_inf_def)
  apply(simp only: justifies_config_def)
    oops
                                        
lemma "({1,2,3}, jctc6_exec) \<in> justifies_config jctc6"
  apply(simp add: justifies_config_def)
  apply(simp add: jctc6_exec_def jctc6_def)
    oops
      
lemma eight_just_2: "8 \<in> C' \<Longrightarrow> is_read 2 jctc6 \<Longrightarrow> (\<exists>y\<in>C'. justifies_event (label_function jctc6 y) (label_function jctc6 2))"
  apply(simp add: jctc6_def)
  apply(blast) -- wtf
  done

  
    
    
lemma "three_just_5": "({Suc 0, 2, 3}, C') \<in> {(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<subseteq> c\<^sub>2 \<and> (\<forall>x\<in>c\<^sub>2. is_read x jctc6 \<longrightarrow> (\<exists>y\<in>c\<^sub>1. justifies_event (label_function jctc6 y) (label_function jctc6 x)))}\<^sup>* \<Longrightarrow>
    8 \<in> C' \<Longrightarrow> is_read 5 jctc6 \<Longrightarrow> \<exists>y\<in>C'. justifies_event (label_function jctc6 y) (label_function jctc6 5)"
  apply(rule_tac x=3 in bexI)
   apply(simp add: jctc6_def)
  apply(insert aej_subset[where es=jctc6, where C="{Suc 0, 2, 3}", where D=C'])
  apply auto
  apply(simp add: justifies_config_star_inf_def justifies_config_subset_def justifies_config_def)
  done

    
lemma foo: "jctc6_C2 \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C' \<Longrightarrow> 8 \<in> C' \<Longrightarrow> 
  \<exists>C''. C' \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C'' \<and> (C'', jctc6_exec) \<in> justifies_config jctc6"
  apply(simp only: justifies_config_star_inf_def)
  apply(simp only: justifies_config_subset_def justifies_config_inf_def)
  apply(simp only: justifies_config_def)
  apply auto
  apply(simp add: jctc6_C2_def jctc6_exec_def)
  apply(rule_tac x=C' in exI)
  apply(rule conjI) 
   prefer 2
   apply(rule conjI)
    apply(rule impI)
    apply(simp only: eight_just_2)
    apply(simp add: three_just_5)
  apply(auto)[1]
  done

lemma "x \<in> C' \<Longrightarrow> is_read x jctc6 \<Longrightarrow> \<exists>y\<in>C'. justifies_event (label_function jctc6 y) (label_function jctc6 x) \<Longrightarrow>    
  (C', C') \<in> {(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<subseteq> c\<^sub>2 \<and> (c\<^sub>1, c\<^sub>2) \<in> justifies_config jctc6}"
  apply(simp add: justifies_config_def)
  apply auto
  apply(rule bexI)
  try
    oops

    
    
lemma foo_two: "jctc6_C2 \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C' \<Longrightarrow> 5 \<in> C' \<Longrightarrow> 
    \<exists>C''. C' \<lesssim>\<^sup>*\<^bsub>jctc6\<^esub> C'' \<and> (C'', jctc6_exec) \<in> justifies_config jctc6"
  apply(rule_tac x="C\<union>{6}" in exI)
  apply(simp add: justifies_config_def)
    oops
    
text {* Similar to the previous argument, whatever the opponent picks in C' we can always add a WA1 
either with event 6 or 8. If 6 or 8 are in C' we can pick C'' = C' and have D, otherwise we must add
one of them to C'' to get D *}
theorem round_2: "(jctc6_C2, jctc6_exec) \<in> {(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<sqsubseteq>\<^bsub>jctc6\<^esub> c\<^sub>2}"
  apply(simp add: ae_justifies_def ae_justifies_subset_def)
    apply(simp add: C2_subset_exec)
    apply (rule allI)
  apply(rule impI)
  apply(case_tac "5 \<in> C'")

    
    
    sorry
    
lemma refl2: "(a, b) \<in> r \<and> (b, c) \<in> r \<Longrightarrow> (a, c) \<in> r\<^sup>*"
  apply auto
  done

theorem rounds: "({}, jctc6_C2) \<in> {(c\<^sub>1, c\<^sub>2).  c\<^sub>1 \<sqsubseteq>\<^bsub>jctc6\<^esub> c\<^sub>2} \<and>
                 (jctc6_C2, jctc6_exec) \<in> {(c\<^sub>1, c\<^sub>2). c\<^sub>1 \<sqsubseteq>\<^bsub>jctc6\<^esub> c\<^sub>2} \<Longrightarrow>
                 ({}, jctc6_exec) \<in> {(c\<^sub>1, c\<^sub>2).  c\<^sub>1 \<sqsubseteq>\<^bsub>jctc6\<^esub> c\<^sub>2}\<^sup>*"
  apply (rule refl2)
  apply auto
  done

theorem jctc6_game: "{} \<sqsubseteq>\<^sup>*\<^bsub>jctc6\<^esub> jctc6_exec"
  apply(simp add: ae_justifies_subset_star_def)
  apply(rule rounds)
  apply(rule conjI)
  apply(rule round_1)
  apply(rule round_2)
  done

  
theorem "well_justified jctc6 jctc6_exec \<and> {2, 5} \<subseteq> jctc6_exec"
  apply(simp add: well_justified_def)
  apply(simp add: jctc_isValid)
  apply(auto)
     apply(simp add: justified_def jctc6_reads jctc6_exec_def jctc6_def)
    apply(simp add: jctc6_game)
   apply(simp add: jctc6_exec_def)
  apply(simp add: jctc6_exec_def)
  done