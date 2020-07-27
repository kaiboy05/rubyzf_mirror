theory Hilbert
imports ZF
begin

axiomatization
  Choose :: "i \<Rightarrow> i"

axiomatization where
  Choose_def: "~(A = 0) \<Longrightarrow> Choose(A):A"

theorem Collect_not_empty: "\<lbrakk> EX x:A. P(x) \<rbrakk> \<Longrightarrow> ~({x:A. P(x)}=0)"
apply(auto)
done

theorem Choose_Collect: "\<And>P. \<lbrakk> EX x:A. P(x) \<rbrakk> \<Longrightarrow> P(Choose({x:A. P(x)}))"
apply(frule Collect_not_empty)
apply(insert Choose_def, auto)
done

theorem skolem_intro: "(ALL t:A. EX z:B. Q(t, z)) \<longleftrightarrow> (EX z1:A\<rightarrow>B. ALL t:A. Q(t, z1 ` t))"
apply(auto)
apply(rule bexI)
proof -
  assume a: "\<forall>t\<in>A. \<exists>z\<in>B. Q(t, z)"
  let ?z1.13 = "(\<lambda> t\<in>A. Choose({x:B. Q(t, x)}))"
  {
    fix t
    assume b: "t:A"
    then have c: "\<exists>z\<in>B. Q(t, z)" using a by(auto)
    then have imp: "Q(t, Choose({x:B. Q(t, x)}))"
      using Choose_Collect[of B "\<lambda> x. Q(t, x)"] by simp
    have d: "Choose({x:B. Q(t, x)}) = (\<lambda> t\<in>A. Choose({x:B. Q(t, x)})) ` t" using b by(auto)
    then have "Q(t, (\<lambda> t\<in>A. Choose({x:B. Q(t, x)})) ` t)" using imp by simp
  } then show "\<forall>t\<in>A. Q(t, ?z1.13 ` t)" by simp
  have e: "(\<lambda> t\<in>A. Choose({x:B. Q(t, x)})) : A \<rightarrow> {Choose({x:B. Q(t', x)}) . t' \<in> A}"
    using lam_funtype[of A "\<lambda> l. Choose({x \<in> B . Q(l, x)})"] by simp
  {
    fix l
    assume b: "l:A"
    then have c: "\<exists>z\<in>B. Q(l, z)" using a by(auto)
    have "{x \<in> B . Q(t, x)} \<subseteq> B" by(auto)
    then have "Choose({x:B. Q(l, x)}):B" 
      using c Choose_def[of "{x \<in> B . Q(l, x)}"] by(auto)
  } then have "{Choose({x:B. Q(t', x)}) . t' \<in> A} \<subseteq> B" 
     using RepFun_subset[of A "\<lambda> l. Choose({x \<in> B . Q(l, x)})" B] by simp
  then show "(\<lambda> t\<in>A. Choose({x:B. Q(t, x)})) : A \<rightarrow> B" 
     using e fun_weaken_type by simp
qed
    
end