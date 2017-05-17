theory EventStructures2
imports Main Relation
begin

datatype mem_action = W | R | I   
datatype label = Label mem_action string int

type_synonym 'a config = "'a set"
  
locale partial_order =
  fixes preceeds :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 50)
    and events :: "'a set" ("\<EE>" 1000)
  assumes refl [intro, simp]: "x \<preceq> x"
    and anti_sym [intro]: "\<lbrakk> x \<preceq> y; y \<preceq> x \<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk> x \<preceq> y; y \<preceq> z \<rbrakk> \<Longrightarrow> x \<preceq> z"

locale labelledES = partial_order + 
  fixes conflict :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "#" 50)
    and label :: "'a \<Rightarrow> label"
  assumes sym [intro]: "\<lbrakk> conflict x y \<rbrakk> \<Longrightarrow> conflict y x"
    and confOverPO [intro]: "\<lbrakk> conflict c d; d \<preceq> e \<rbrakk> \<Longrightarrow> conflict c e"


end