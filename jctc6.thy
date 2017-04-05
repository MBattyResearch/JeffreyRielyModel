theory jctc6
  imports EventStructures String Relation Transitive_Closure 
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
  
lemma symm_imp_symm_trancl: "symmetric r \<longrightarrow> symmetric (r\<^sup>+)"
  apply(auto simp add: symmetric_def)
  apply(erule trancl.induct[where ?P = "\<lambda>a b. (b, a) \<in> r\<^sup>+"])
  apply auto
   apply(meson trancl_into_trancl2)
  apply(erule trancl.induct[where ?P = "\<lambda>a b. (b, a) \<in> r\<^sup>+"])
    apply auto
  apply(meson trancl_into_trancl2)
  done

lemma symm_pc: "symmetric ((symmetriccl r)\<^sup>+)"
  apply(simp add: symmetric_def)
  by (meson symm_imp_symm_trancl symmetric_def symmetric_symmetriccl)

lemma jctc6_symm_conflict: "symmetric ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(simp add: symmetric_def)
  apply (meson symm_pc symmetric_def)
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

lemma alg_subset: "a \<subseteq> c \<union> b \<Longrightarrow> a - b \<subseteq> c"
  by auto

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
    
thm "justifies_event.induct"
thm "justifies_event.cases"
  
theorem "\<exists>C . well_justified jctc6 C \<and> {2, 5} \<subseteq> C"
  apply(simp add: well_justified_def)
  apply(simp add: jctc_isValid)
  apply(simp add: justified_def ae_justifies_star_def ae_justifies_def)
  apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
  apply(simp add: justifies_config_def)
  apply(induct rule: justifies_event.cases)
        apply auto[1]
       apply simp
          apply auto[1]
         apply simp
  oops
    