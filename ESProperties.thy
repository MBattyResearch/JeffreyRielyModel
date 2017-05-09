theory ESProperties
imports EventStructures String
begin
  
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
    
end
