theory RelationalLemmas
  imports Main Relation Transitive_Closure
begin
  
definition symmetric:: "'a rel \<Rightarrow> bool" where
  "symmetric r \<equiv> \<forall>a b . (a, b) \<in> r \<longleftrightarrow> (b, a) \<in> r"
      
definition symmetriccl:: "'a rel \<Rightarrow> 'a rel" where
  "symmetriccl r \<equiv> {(y, x) . (x, y) \<in> r} \<union> r"
  
lemma symmetric_symmetriccl: "\<forall>r . sym (symmetriccl r)"
  apply(simp add: sym_def symmetriccl_def)
  done
    
lemma symm_imp_symm_trancl: "sym r \<longrightarrow> sym (r\<^sup>+)"
  apply(auto simp add: sym_def)
  apply(erule trancl.induct[where ?P = "\<lambda>a b. (b, a) \<in> r\<^sup>+"])
  apply auto
   apply(meson trancl_into_trancl2)
  done

lemma symm_pc: "sym ((symmetriccl r)\<^sup>+)"
  apply(simp add: sym_def)
  by (meson  symm_imp_symm_trancl sym_def symmetric_symmetriccl)

end
  