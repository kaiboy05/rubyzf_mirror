theory Signal
imports Nlist IntExt Hilbert ZF.Univ
begin

consts
  "time" :: "i"
  "BaseChTy" :: "i"

axiomatization where
  nat_in_base: "nat:BaseChTy"

syntax
  "sig" :: "i \<Rightarrow> i"
  "time" :: "i"
translations
  "time" == "CONST int"
  "sig(A)" == "CONST time \<rightarrow> A"

definition ChEl :: "i" where
  "ChEl == univ(Union(BaseChTy))"

definition ChTy :: "i" where
  "ChTy == Pow(ChEl)"

definition spair :: "[i, i] \<Rightarrow> i" ("(<_#/_>)") where
  "<a # b> == (lam t:time. <a`t, b`t>)"

definition scons :: "[i, i, i] \<Rightarrow> i" ("([_@>_|/_])") where
  "[a @> l | n] == (lam t:time. ncons(n, a`t, l`t))"

definition snil :: "i" where
  "snil == (lam t:time. nnil)"

definition sapp :: "[i, i, i, i] \<Rightarrow> i" where
  "sapp(n1, n2, l1, l2) == (lam t:time. napp(n1, n2, l1`t, l2`t))"

definition ssnoc :: "[i, i, i] \<Rightarrow> i" ("([_<@_|/_])") where
  "[l <@ a | n] == (lam t:time. nsnoc(n, l`t, a`t))"

definition pri :: "i \<Rightarrow> i" where
  "pri(a) == (lam t:time. fst(a`t))"

definition sec :: "i \<Rightarrow> i" where
  "sec(a) == (lam t:time. snd(a`t))"

find_theorems name: sig

theorem sig_mono: "\<lbrakk> A \<subseteq> B \<rbrakk> \<Longrightarrow> sig(A) \<subseteq> sig(B)"
oops

theorem sig_sub_func: "\<lbrakk> x:sig(A); \<And>t. t:int \<Longrightarrow> x`t:B \<rbrakk> \<Longrightarrow> x:sig(B)"
oops

theorem nlist_in_chty: "\<lbrakk> A:ChTy \<rbrakk> \<Longrightarrow> nlist[n]A:ChTy"
oops

theorem prod_in_chty: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> A*B:ChTy"
oops

theorem spair_chel: "\<lbrakk> a:sig(ChEl); b:sig(ChEl) \<rbrakk> \<Longrightarrow> <a # b>:sig(ChEl)"
oops

theorem spair_type: "\<lbrakk> a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <a # b>:sig(A*B)"
oops

theorem scons_type: "\<lbrakk> a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> [a @> l|n]:sig(nlist[succ(n)]A)"
oops

theorem snil_type: "snil:sig(nlist[0]A)"
oops

theorem sapp_type: 
  "\<lbrakk> n1:nat; n2:nat; l1:sig(nlist[n1]A); l2:sig(nlist[n2]A) \<rbrakk> \<Longrightarrow> sapp(n1, n2, l1, l2):X"
oops

theorem ssnoc_type: "\<lbrakk>  n:nat; a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> [l <@ a|n]:sig(nlist[succ(n)]A)"
oops

theorem ssnoc_is_app: "[l <@ a|n] = sapp(n, 1, l, [a @> snil|0])"
oops

theorem spair_iff: 
  "\<lbrakk> x1:sig(A); x2:sig(B); x1a:sig(C); x2a:sig(D) \<rbrakk> 
    \<Longrightarrow> <x1 # x2> = <x1a # x2a> \<longleftrightarrow> x1 = x1a & x2 = x2a"
oops

theorem spairD: 
  "\<lbrakk> <x1 # x2> = <x1a # x2a>; x1:sig(A); x2:sig(B); x1a:sig(C); x2a:sig(D) \<rbrakk> 
    \<Longrightarrow> x1 = x1a & x2 = x2a"
oops

theorem spair_inject: 
  "\<lbrakk> <x1 # x2> = <x1a # x2a>; x1:sig(A); x2:sig(B); x1a:sig(C); x2a:sig(D);
    \<lbrakk> x1 = x1a; x2 = x2a \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
oops

theorem func_nhd_ntl: 
  "\<lbrakk> l:sig(nlist[succ(n)]A) \<rbrakk> 
    \<Longrightarrow> l = (lam t:time. ncons(n, (lam t1:time. nhd(l ` t1)) ` t, 
                                  (lam t1:time. ntl(succ(n), l`t1))`t ))"
oops

theorem func_nfront_nlast: 
  "\<lbrakk> l:sig(nlist[succ(n)]A) \<rbrakk> 
    \<Longrightarrow> l = sapp(n, 1, (lam t:time. nfront(succ(n), l`t)), [(lam t:time. nlast(l`t)) @> snil |0])"
oops

theorem ssnoc_iff: 
  "\<lbrakk> a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E) \<rbrakk>
    \<Longrightarrow> ([la <@ a |n] = [lb <@ b |n]) \<longleftrightarrow> (la = lb & a = b)"
oops

theorem scons_iff: 
  "\<lbrakk> a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E) \<rbrakk>
    \<Longrightarrow> ([a @> la |n] = [b @> lb |n]) \<longleftrightarrow> (la = lb & a = b)"
oops

theorem ssnoc_inject: 
  "\<lbrakk> ([la <@ a |n] = [lb <@ b |n]); a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E); 
    \<lbrakk>la = lb; a = b\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
oops

theorem scons_inject:
  "\<lbrakk> ([a @> la |n] = [b @> lb |n]); a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E); 
    \<lbrakk>la = lb; a = b\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
oops

theorem scons_iff2: 
  "\<lbrakk> a:sig(A); la:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n1]E) \<rbrakk>
    \<Longrightarrow> ([a @> la |n] = [b @> lb |n1]) \<longleftrightarrow> (la = lb & a = b & n = n1)"
oops

theorem sapp_snil:
  "\<lbrakk> l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> sapp(0, n, snil, l) = l"
oops

theorem sapp_scons: 
  "\<lbrakk> a:sig(A); la:sig(nlist[na]A); lb:sig(nlist[nb]A) \<rbrakk> 
    \<Longrightarrow> sapp(succ(na), nb, [a @> la | na], lb) = [a @> sapp(na, nb, la, lb) | (na #+ nb)]"
oops

theorem scons_ssnoc: "\<lbrakk> a:sig(A) \<rbrakk> \<Longrightarrow> [a @> snil |0] = [snil <@ a |0]"
oops

theorem sig_pairE: "\<lbrakk> c:sig(A*B); \<And>a b. \<lbrakk> c = <a # b>; a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
oops

theorem sig_nlist0E: "\<lbrakk> c:sig(nlist[0]A); c=snil \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
oops

theorem sig_nlistE: 
  "\<lbrakk> c:sig(nlist[succ(n)]A); \<And>a l. \<lbrakk> c = [a @> l | n]; a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
oops

theorem sig_ssnocE:
  "\<lbrakk> x:sig(nlist[succ(n)]A); \<lbrakk> a:sig(A); l:sig(nlist[n]A); x= [l <@ a |n] \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
oops

theorem pri_iff: "\<lbrakk> a:sig(A) \<rbrakk> \<Longrightarrow> pri(<a # b>) = a"
oops

theorem sec_iff: "\<lbrakk> b:sig(B) \<rbrakk> \<Longrightarrow> sec(<a # b>) = b"
oops

end