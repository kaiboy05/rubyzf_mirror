theory Relation
imports Signal
begin

definition dtyp :: "i \<Rightarrow> i" where
  "dtyp(R) == range(Union(domain(R)))"

definition rtyp :: "i \<Rightarrow> i" where
  "rtyp(R) == range(Union(range(R)))"

definition ddtyp :: "i \<Rightarrow> i" where
  "ddtyp(R) == domain(dtyp(R))"

definition rdtyp :: "i \<Rightarrow> i" where
  "rdtyp(R) == range(dtyp(R))"

definition rrtyp :: "i \<Rightarrow> i" where
  "rrtyp(R) == range(rtyp(R))"

definition drtyp :: "i \<Rightarrow> i" where
  "drtyp(R) == domain(rtyp(R))"

syntax
  "@rel" :: "[i, i] \<Rightarrow> i"  (\<open>(_~/_)\<close> [73, 72] 72)
  "@srel" :: "[i, i] \<Rightarrow> i" (\<open>(_<~>/_)\<close> [73, 72] 72)
translations
  "A~B" == "CONST Pow(A * B)"
  "A<~>B" == "sig(A)~sig(B)"

theorem rel_extension: "\<lbrakk> c:A; A:B~C; \<And> x y. \<lbrakk> <x, y> = c; <x,y>:A \<rbrakk> \<Longrightarrow>P \<rbrakk> \<Longrightarrow> P"
apply(blast)
done

theorem subset_rel: "\<lbrakk> \<And>x. x:A \<Longrightarrow> A:C~D; \<And>x y. \<lbrakk> <x, y>:A \<rbrakk> \<Longrightarrow> <x, y>:B \<rbrakk> \<Longrightarrow> A \<subseteq> B"
apply(blast)
done

theorem mem_rel_type: "\<lbrakk> <x, y>:R; R:A~B \<rbrakk> \<Longrightarrow> x:A & y:B"
apply(blast)
done

theorem mem_rel_dtype: "\<lbrakk> <x, y>:R; R:A~B \<rbrakk> \<Longrightarrow> x:A"
apply(blast)
done

theorem mem_rel_rtype: "\<lbrakk> <x, y>:R; R:A~B \<rbrakk> \<Longrightarrow> y:B"
apply(blast)
done

theorem dtyp_sig: "\<lbrakk> <x, y>:R; x:sig(A) \<rbrakk> \<Longrightarrow> x:sig(dtyp(R))"
apply(rule sig_sub_func, simp)
apply(frule apply_rangeI, simp)
apply(auto simp add: dtyp_def)
done

theorem rtyp_sig: "\<lbrakk> <x, y>:R; y:sig(A) \<rbrakk> \<Longrightarrow> y:sig(rtyp(R))"
apply(rule sig_sub_func, simp)
apply(frule apply_rangeI, simp)
apply(auto simp add: rtyp_def)
done

lemma range_sub: "A \<subseteq> B \<Longrightarrow> range(A) \<subseteq> range(B)"
apply(auto)
done

lemma domain_sub: "A \<subseteq> B \<Longrightarrow> domain(A) \<subseteq> domain(B)"
apply(auto)
done

lemma range_Union: "range(Union(sig(A))) \<subseteq> A"
apply(auto)
apply(drule range_type, simp+)
done

theorem dtyp_rel: "\<lbrakk> R \<subseteq> (sig(A))*(sig(B)); x:sig(dtyp(R)) \<rbrakk> \<Longrightarrow> x:sig(A)"
apply(rule sig_sub_func, simp)
apply(frule domain_rel_subset)
apply(simp add: dtyp_def)
apply(drule Union_mono) back
apply(drule range_sub) back
apply(insert range_Union[of A], drule subset_trans, simp)
apply(drule apply_funtype, simp)
apply(insert subsetD[of "range(\<Union>domain(R))"], simp)
done

theorem rtyp_rel: "\<lbrakk> R \<subseteq> (sig(A))*(sig(B)); x:sig(rtyp(R)) \<rbrakk> \<Longrightarrow> x:sig(B)"
apply(rule sig_sub_func, simp)
apply(frule range_rel_subset)
apply(simp add: rtyp_def)
apply(drule Union_mono) back
apply(drule range_sub) back
apply(insert range_Union[of B], drule subset_trans, simp)
apply(drule apply_funtype, simp)
apply(insert subsetD[of "range(\<Union>range(R))"], simp)
done

theorem sub_dtyp_rtyp: "R:A<~>B \<Longrightarrow> R:dtyp(R) <~> rtyp(R)"
apply(auto)
apply(drule subsetD, simp)
apply(auto)
apply(rule dtyp_sig, simp+)
apply(rule rtyp_sig, simp+)
done

theorem sub_dtyp_rtypI: "\<lbrakk> A:A2<~>B2; c:A \<rbrakk> \<Longrightarrow> c:(sig(dtyp(A)))*(sig(rtyp(A)))"
apply(auto)
apply(drule subsetD, simp)
apply(auto)
apply(rule dtyp_sig, simp+)
apply(rule rtyp_sig, simp+)
done

lemma domain_time_range_extension: "\<lbrakk> x: Sigma(A, B); x:R \<rbrakk> \<Longrightarrow> x:domain(R)*range(R)"
apply(auto)
done

theorem sub_ddtyp_rrtyp: "R:(A*B)<~>(C*E) \<Longrightarrow> R:ddtyp(R)*rdtyp(R)<~>drtyp(R)*rrtyp(R)"
apply(auto)
apply(frule PowI)
apply(erule rel_extension, simp)
apply(auto simp add: ddtyp_def rdtyp_def)
apply(frule mem_rel_dtype, simp)
apply(frule dtyp_sig, simp)
apply(rule sig_sub_func, simp)
apply(frule apply_funtype, simp)
apply(frule apply_funtype, simp) back
apply(rule domain_time_range_extension, simp+)
apply(auto simp add: drtyp_def rrtyp_def)
apply(frule mem_rel_rtype, simp)
apply(frule rtyp_sig, simp)
apply(rule sig_sub_func, simp)
apply(frule apply_funtype, simp)
apply(frule apply_funtype, simp) back
apply(rule domain_time_range_extension, simp+)
done

theorem ddtyp_rel: "\<lbrakk> x:sig(ddtyp(R)); R:A*B<~>C*E \<rbrakk> \<Longrightarrow> x:sig(A)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, (simp add: ddtyp_def dtyp_def)+)
apply(frule domain_rel_subset)
apply(drule Union_mono) back
apply(drule range_sub) back
apply(insert range_Union[of "A*B"], drule subset_trans, simp)
apply(drule domain_sub) back back
apply(blast)
done

theorem rdtyp_rel: "\<lbrakk> x:sig(rdtyp(R)); R:A*B<~>C*E \<rbrakk> \<Longrightarrow> x:sig(B)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, (simp add: rdtyp_def dtyp_def)+)
apply(frule domain_rel_subset)
apply(drule Union_mono) back
apply(drule range_sub) back
apply(insert range_Union[of "A*B"], drule subset_trans, simp)
apply(drule range_sub) back back
apply(blast)
done

theorem rrtyp_rel: "\<lbrakk> x:sig(rrtyp(R)); R:A*B<~>C*E \<rbrakk> \<Longrightarrow> x:sig(E)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, (simp add: rrtyp_def rtyp_def)+)
apply(frule range_rel_subset)
apply(drule Union_mono) back
apply(drule range_sub) back
apply(insert range_Union[of "C*E"], drule subset_trans, simp)
apply(drule range_sub) back back
apply(blast)
done

theorem drtyp_rel: "\<lbrakk> x:sig(drtyp(R)); R:A*B<~>C*E \<rbrakk> \<Longrightarrow> x:sig(C)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, (simp add: drtyp_def rtyp_def)+)
apply(frule range_rel_subset)
apply(drule Union_mono) back
apply(drule range_sub) back
apply(insert range_Union[of "C*E"], drule subset_trans, simp)
apply(drule domain_sub) back back
apply(blast)
done

lemma "a:sig(A) \<Longrightarrow> a:domain(range(\<lambda>t\<in>time. <a`t, b(t)>))"
oops

theorem ddtyp_sig: "\<lbrakk> x:sig(A); <<x#x2>, y>:R \<rbrakk> \<Longrightarrow> x:sig(ddtyp(R))"
apply(simp add: ddtyp_def dtyp_def spair_def)
apply(rule sig_sub_func, simp)
oops

thm apply_rangeI

find_theorems range
find_theorems "_:_" "_\<subseteq>_"
find_theorems "_\<Longrightarrow>_:Sigma(_,_)"

theorem rdtyp_sig: "\<lbrakk> x:sig(A); <<x1#x>, y>:R \<rbrakk> \<Longrightarrow> x:sig(rdtyp(R))"
oops

theorem rrtyp_sig: "\<lbrakk> x:sig(A); <x, <y1#y>>:R \<rbrakk> \<Longrightarrow> y:sig(rrtyp(R))"
oops

theorem drtyp_sig: "\<lbrakk> x:sig(A); <x, <y#y2>>:R \<rbrakk> \<Longrightarrow> y:sig(drtyp(R))"
oops

theorem dddtyp_rel: "\<lbrakk> x:sig(domain(ddtyp(R))); R:(A*A1)*B<~>C*E \<rbrakk> \<Longrightarrow> x:sig(A)"
oops

theorem rddtyp_rel: "\<lbrakk> x:sig(range(ddtyp(R))); R:(A1*A)*B<~>C*E \<rbrakk> \<Longrightarrow> x:sig(A)"
oops

theorem drrtyp_rel: "\<lbrakk> x:sig(range(ddtyp(R))); R:A*B<~>C*(E*E1) \<rbrakk> \<Longrightarrow> x:sig(E)"
oops

theorem dddtyp_sig: "\<lbrakk> x:sig(A); <<<x#x2>#x3>, y>:R \<rbrakk> \<Longrightarrow> x:sig(domain(ddtyp(R)))"
oops

theorem drrtyp_sig: "\<lbrakk> x:sig(A); <y, <x1#<x#x3>>>:R \<rbrakk> \<Longrightarrow> x:sig(domain(rrtyp(R)))"
oops

theorem drrtyp_sig: "\<lbrakk> x:sig(A); <<<x1#x>#x3>, y>:R \<rbrakk> \<Longrightarrow> x:sig(range(ddtyp(R)))"
oops
  
end