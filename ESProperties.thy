theory ESProperties
imports EventStructures ExampleEventStructures String
begin
  
lemma ae_justifies_refl[simp]: "C \<lesssim>\<^sup>*\<^bsub>es\<^esub> C"
  apply(simp add: justifies_config_star_inf_def)
  done

lemma aej_subset: "C \<lesssim>\<^sup>*\<^bsub>es\<^esub> D \<Longrightarrow> C \<subseteq> D"
  apply(simp only: justifies_config_star_inf_def)
  apply(rule rtrancl_induct[where a=C, where b=D, where r="justifies_config_subset es", 
        where P="\<lambda>x . C \<subseteq> x"])
    apply(auto simp add: justifies_config_subset_def)
  done
    
lemma ref_impl: "C \<lesssim>\<^bsub>es\<^esub> C' \<Longrightarrow> C' \<lesssim>\<^bsub>es\<^esub> C'"
  apply(simp add: justifies_config_inf_def justifies_config_subset_def justifies_config_def)
  apply clarsimp
  apply blast
  done
      
lemma add_write_okay: "C' \<lesssim>\<^bsub>es\<^esub> C' \<Longrightarrow> \<not>(is_read ev es) \<Longrightarrow> C' \<lesssim>\<^bsub>es\<^esub> C' \<union> {ev}"
  apply(simp only: justifies_config_inf_def justifies_config_def)
  apply(simp (no_asm) add: justifies_config_subset_def justifies_config_def)
  apply auto
  apply(simp add: justifies_config_subset_def justifies_config_def)
  done 
    
lemma add_write_really_okay: "C \<lesssim>\<^bsub>es\<^esub> C' \<Longrightarrow> \<not>(is_read ev es) \<Longrightarrow> C' \<lesssim>\<^bsub>es\<^esub> C' \<union> {ev}"
  apply(rule add_write_okay)
  apply(rule ref_impl)
   apply assumption+
  done

lemma just_in_rjuststar: "C \<lesssim>\<^bsub>es\<^esub> C' \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> C'"
  apply(simp add: justifies_config_star_inf_def)
  apply(rule r_into_rtrancl)
  apply(simp add: justifies_config_inf_def)
  done

lemma add_write_super_okay: "C \<lesssim>\<^bsub>es\<^esub> C' \<Longrightarrow> \<not>(is_read ev es) \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> C' \<union> {ev}"
  apply(rule just_in_rjuststar)
  apply(simp only: justifies_config_inf_def)
  apply(simp only: justifies_config_subset_def)
  apply(simp only: justifies_config_def)
  apply auto
  done 
  
lemma "C \<noteq> C' \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> C' \<Longrightarrow> \<not>(is_read ev es) \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> C' \<union> {ev}"
  apply(rule just_in_rjuststar)
  apply(simp only: justifies_config_inf_def justifies_config_star_inf_def)
  apply(simp only: justifies_config_subset_def)
  apply(simp only: justifies_config_def)
  try
  oops
    

lemma just_config_imp_round: "(C, D) \<in> justifies_config es \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> C' \<Longrightarrow> (\<exists>C'' . C' \<lesssim>\<^sup>*\<^bsub>es\<^esub> C'' \<longrightarrow> (C'', D) \<in> justifies_config es)"
  apply(rule exI)
  apply(rule impI)
  apply(frule ae_justifies_refl)
  done
    
-- {* For every step of adding something to C' we have that the previous steps are included, so any
      "dependants" remain.
      Mark: in the final step (C_0,C') , all reads in C' are justified by C_0, and C_0 is a subset,
      so all reads in C' are justified by writes in C'. *}
lemma aejrefl_and_aejstar_imp_aej: "C \<lesssim>\<^bsub>es\<^esub> C \<Longrightarrow> C \<lesssim>\<^sup>*\<^bsub>es\<^esub> C' \<Longrightarrow> C' \<lesssim>\<^bsub>es\<^esub> C'"
  apply(simp add: justifies_config_star_inf_def)
  apply(simp add: rtrancl_eq_Id_trancl)
    apply(erule disjE)
   apply(simp_all)
  apply(simp add: trancl_unfold_right)
  apply(simp add: justifies_config_subset_def justifies_config_def)
  apply clarsimp
  apply(rename_tac "C\<^sub>0")
  apply(simp add: justifies_config_inf_def justifies_config_subset_def justifies_config_def)
  apply(rule ballI)
  apply blast
  done

lemma just_star_imp_just: "\<C> \<lesssim>\<^sup>*\<^bsub>es\<^esub> C' \<Longrightarrow> C' \<lesssim>\<^bsub>es\<^esub> C'"
  apply(rule aejrefl_and_aejstar_imp_aej [where C=\<C>])
   apply(simp add: emptyESJustEmptyES)
  apply(assumption)
  done
    
lemma just_config_star_split: "A \<lesssim>\<^bsub>es\<^esub> B \<Longrightarrow> B \<lesssim>\<^bsub>es\<^esub> C \<Longrightarrow> A \<lesssim>\<^sup>*\<^bsub>es\<^esub> C"
  apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
  done

lemma just_config_star_splitL: "A \<lesssim>\<^sup>*\<^bsub>es\<^esub> B \<Longrightarrow> B \<lesssim>\<^bsub>es\<^esub> C \<Longrightarrow> A \<lesssim>\<^sup>*\<^bsub>es\<^esub> C"    
  apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
  done
    
lemma just_config_star_splitR: "A \<lesssim>\<^bsub>es\<^esub> B \<Longrightarrow> B \<lesssim>\<^sup>*\<^bsub>es\<^esub> C \<Longrightarrow> A \<lesssim>\<^sup>*\<^bsub>es\<^esub> C"    
  apply(simp add: justifies_config_star_inf_def justifies_config_inf_def)
  done

end
