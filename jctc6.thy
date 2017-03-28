theory jctc6
imports EventStructures String "$AFP/Transitive-Closure/Transitive_Closure_List_Impl"
begin

definition jctc6 :: "string event_structure" where
"jctc6 \<equiv> \<lparr> 
    event_set = { ''a'', ''b'', ''c'', ''d'', ''e'', ''f'', ''g'', ''h'' },
    primitive_order =  { (''a'', ''g''), (''a'', ''e''), (''a'', ''d''), (''a'', ''b''), (''g'', ''h''), (''b'', ''c''), (''e'', ''f'') },
    primitive_conflict = { (''e'', ''g''), (''b'', ''d'') },
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
   apply(erule trancl.induct[where ?P = "\<lambda>a b. (b, a) \<in> r\<^sup>+"], auto, meson trancl_into_trancl2)+
  done

lemma symm_pc: "symmetric ((symmetriccl r)\<^sup>+)"
  apply(simp add: symmetric_def)
  by (meson symm_imp_symm_trancl symmetric_def symmetric_symmetriccl)

lemma jctc6_symm_conflict: "symmetric ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(simp add: symmetric_def)
  apply (meson symm_pc symmetric_def)
  done
    

    
lemma jctc6_is_conf_valid: "isConfValid ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(simp add: isConfValid_def)
    apply(auto)
   apply(simp add: jctc6_symm_conflict)
  apply(simp add: trans_rtrancl)
  done
                      
value "memo_list_rtrancl [(''e'', ''g''), (''b'', ''d'')]"
    
lemma jctc6_is_minimal: "minimal ((primitive_order jctc6)\<^sup>*) ((symmetriccl (primitive_conflict jctc6))\<^sup>+ - Id)"
  apply(simp add: minimal_def jctc6_def symmetriccl_def symmetric_def)
  apply auto
  apply (erule rtrancl.cases)
    apply simp
        
  -- \<open> Do clever induction thingy with that where syntax, yo! \<close>

    
   
    
  sorry
  
theorem jctc_isValid: "isValidES jctc6"
  apply(simp add: isValidES_def)
  apply(simp add: jctc6_is_finite)
  apply(simp add: jctc6_valid_PO)
  apply(simp add: jctc6_is_minimal)
  apply(simp add: jctc6_is_conf_valid)
  done
    
thm "justifies_event.induct"
thm "justifies_event.cases"
  
theorem "\<exists>C . well_justified jctc6 C \<and> {''b'', ''e''} \<subseteq> C"
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
    