theory EventStructures2
imports Main Relation
begin

locale partial_order =
  fixes preceeds :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 50)
  fixes events :: "'a set" ("\<EE>" 1000)
  assumes refl [intro, simp]: "x \<preceq> x"
    and anti_sym [intro]: "\<lbrakk> x \<preceq> y; y \<preceq> x \<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk> x \<preceq> y; y \<preceq> z \<rbrakk> \<Longrightarrow> x \<preceq> z"

locale primeES = partial_order + 
  fixes conflict :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "#" 50)
  assumes sym [intro]: "\<lbrakk> conflict x y \<rbrakk> \<Longrightarrow> conflict y x"
    and confOverPO [intro]: "\<lbrakk> conflict c d; d \<preceq> e \<rbrakk> \<Longrightarrow> conflict c e"

datatype mem_action = W | R | I   
datatype label = Label mem_action string int
type_synonym 'a config = "'a set"

locale labelledES = primeES + 
  fixes label :: "'a \<Rightarrow> label"
  fixes config_domain :: "'a config set" ("\<CC>" 1000)
  assumes conflict_free: "\<lbrakk>C \<in> config_domain; x \<in> C; y \<in> C \<rbrakk> \<Longrightarrow> \<not>(conflict x y)"
    and down_closed: "\<lbrakk>C \<in> config_domain; y \<in> C; x \<preceq> y \<rbrakk> \<Longrightarrow> x \<in> C"
    and config_subset: "C \<in> \<CC> \<Longrightarrow> C \<subseteq> \<EE>"



end