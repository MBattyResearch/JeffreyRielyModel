theory EventStructures2
imports Main Relation
begin

datatype mem_action = W | R | I   
datatype label = Label mem_action string int

type_synonym 'a config = "'a set"
  
locale partial_order =
  fixes preceeds :: "'a rel" 
    and events :: "'a set" ("\<EE>" 1000)
  assumes "refl preceeds"
    and "antisym preceeds"
    and "trans preceeds"

locale labelledES = partial_order + 
  fixes conflict :: "'a rel"
    and label :: "'a \<Rightarrow> label"
  assumes "sym conflict"
    and confOverPO [intro]: "\<lbrakk> (c, d)\<in>conflict; (d, e)\<in>preceeds \<rbrakk> \<Longrightarrow> (c,e)\<in>conflict"


end