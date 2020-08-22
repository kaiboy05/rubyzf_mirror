theory Wiring
imports RubyType
begin

definition Id :: "i \<Rightarrow> i" where
  "Id(A) == spread({xy:A*A. EX x. xy = <x, x>})"

definition lwir :: "[i, i] \<Rightarrow> i" where
  "lwir(A, C) == spread({ab:A*(A*(C*C)). EX a c. ab = <a, <a, <c, c>>>})"

definition rwir :: "[i, i] \<Rightarrow> i" where
  "rwir(A, C) == spread({ab:(A*(A*C))*C. EX b c. ab = <<c, <c, b>>, b>})"

definition reorg :: "[i, i, i] \<Rightarrow> i" where
  "reorg(A, B, C) == spread({ab:((A*B)*C)*(A*(B*C)). 
    EX a b c. ab = <<<a,b>,c>,<a, <b, c>>>})"

definition cross :: "[i, i] \<Rightarrow> i" where
  "cross(A, B) == spread({ab:((A*B)*(B*A)). EX a b. ab = <<a,b>, <b,a>>})"

definition p1 :: "[i, i] \<Rightarrow> i" where
  "p1(A, B) == spread({ab:(A*B)*A. EX a b. ab = <<a,b>, a>})"

definition p2 :: "[i, i] \<Rightarrow> i" where
  "p2(A, B) == spread({ab:(A*B)*B. EX a b. ab = <<a,b>, b>})"

definition dub :: "i \<Rightarrow> i" where
  "dub(A) == spread({ab:A*(A*A). EX a. ab = <a, <a,a>>})"

definition pzip :: "[i, i, i, i] \<Rightarrow> i" where
  "pzip(A, B, C, E) == 
    spread({ab: (((A*B)*(C*E))*((A*C)*(B*E))). 
    EX a b c d. ab = <<<a, b>, <c, d>>, <<a, c>, <b, d>>>})"

definition NNIL :: "i" where
  "NNIL == spread({<nnil, nnil>})"

definition apl :: "[i, i] \<Rightarrow> i" where
  "apl(A, n) == spread({ab:(A*nlist[n]A)*nlist[succ(n)]A.
  EX a1 a2. ab = <<a1, a2>, ncons(n, a1, a2)>})"

definition apr :: "[i, i] \<Rightarrow> i" where
  "apr(A, n) == spread({ab:(nlist[n]A*A)*nlist[succ(n)]A.
  EX a1 a2. ab = <<a1, a2>, nsnoc(n, a1, a2)>})"

definition app :: "[i, i, i] \<Rightarrow> i" where
  "app(A, n, m) == spread({ab:(nlist[n]A*nlist[m]A)*nlist[n+m]A.
  EX a1 a2. ab = <<a1, a2>, napp(n, m, a1, a2)>})"

theorem reorg_type: "reorg(A,B,C): (A*B)*C <~>A*B*C"
apply(unfold reorg_def)
apply(rule spread_type, blast)
done

theorem reorgR: "\<lbrakk> A:ChTy; B:ChTy; C:ChTy \<rbrakk> \<Longrightarrow> reorg(A,B,C):(A*B)*C<R>A*B*C"
apply(unfold reorg_def)
apply(rule spreadR)
apply((intro prod_in_chty, simp+)+, blast)
done

lemma spair_apply_time: "t:int \<Longrightarrow> <a#b>`t = <a`t, b`t>"
apply(simp add: spair_def)
done

lemma sig_apply_time: "\<lbrakk> a:sig(A); t:int \<rbrakk> \<Longrightarrow> a`t:A"
apply(simp)
done

theorem reorgI: 
  "\<lbrakk> a:sig(A); b:sig(B); c:sig(C) \<rbrakk> \<Longrightarrow> <<<a#b>#c>,<a#<b#c>>>:reorg(A,B,C)"
apply(unfold reorg_def)
apply(rule spreadI)
apply(rule, rule)
apply((subst spair_apply_time, simp)+)
apply((drule sig_apply_time, simp)+)
apply(simp)
apply((subst spair_apply_time, simp)+)
apply(simp)
apply(blast)
apply((intro spair_type, simp+)+)
done

theorem reorgE:
  "\<lbrakk> <<<a#b>#c>,<d#<e#f>>>:reorg(A,B,C); 
    \<lbrakk> a=d; b=e; c=f \<rbrakk> \<Longrightarrow> P;
    a:sig(A'); b:sig(B'); c:sig(C');
    d:sig(A''); e:sig(B''); f:sig(C'') \<rbrakk> \<Longrightarrow> P"
apply(unfold reorg_def)
apply(erule spreadE)
apply(subgoal_tac "a=d & b=e & c=f", simp)
apply(intro conjI)
apply((rule fun_extension, simp+,
      drule bspec, simp,
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem cross_type: "cross(A,B):A*B<~>B*A"
apply(unfold cross_def)
apply(rule spread_type, blast)
done

theorem crossR: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> cross(A,B):A*B<R>B*A"
apply(unfold cross_def)
apply(rule spreadR)
apply((intro prod_in_chty, simp+)+, blast)
done

theorem crossI: "\<lbrakk> a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <<a#b>, <b#a>>:cross(A,B)"
apply(unfold cross_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast)
apply((intro spair_type, simp+)+)
done

theorem crossE: 
  "\<lbrakk> <<a#b>, <c#d>>:cross(A,B); \<lbrakk> a=d; b=c \<rbrakk> \<Longrightarrow> P;
    a:sig(A'); b:sig(B'); c:sig(B''); d:sig(A'') \<rbrakk> \<Longrightarrow> P"
apply(unfold cross_def, erule spreadE)
apply(subgoal_tac "a=d & b=c", simp)
apply(rule)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem Id_type: "Id(A):A<~>A"
apply(unfold Id_def)
apply(rule spread_type, blast)
done

theorem IdR: "A:ChTy \<Longrightarrow> Id(A):A<R>A"
apply(unfold Id_def, rule spreadR)
apply((simp | blast)+)
done

theorem IdI: "a:sig(A) \<Longrightarrow> <a,a>:Id(A)"
apply(unfold Id_def, rule spreadI, rule)
apply((simp | blast)+)
done

theorem IdI2: "\<lbrakk> a:sig(A); b:sig(B); a=b \<rbrakk> \<Longrightarrow> <a, b>:Id(A)"
apply(simp, rule IdI, simp)
done

theorem IdE: "\<lbrakk> <x,y>:Id(A); \<lbrakk> x=y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold Id_def)
apply(subgoal_tac "x:sig(A) & y:sig(A)")
apply(erule spreadE)
apply(subgoal_tac "x=y", simp)
apply(rule fun_extension, auto)
apply(unfold spread_def, auto)
apply(subgoal_tac "domain({xy \<in> A \<times> A . \<exists>x. xy = \<langle>x, x\<rangle>}) \<subseteq> A")
apply(drule sig_mono, rule subsetD, simp+, blast)
apply(subgoal_tac "range({xy \<in> A \<times> A . \<exists>x. xy = \<langle>x, x\<rangle>}) \<subseteq> A")
apply(drule sig_mono, rule subsetD, simp+, blast)
done

theorem lwir_type: "lwir(A,B):A<~>A*B*B"
apply(unfold lwir_def, rule spread_type, blast)
done

theorem lwirR: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> lwir(A,B):A<R>A*B*B"
apply(unfold lwir_def, rule spreadR)
apply(((intro prod_in_chty)?, simp)+)
apply(blast)
done

theorem lwirI: "\<lbrakk> a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <a, <a#<b#b>>>:lwir(A,B)"
apply(unfold lwir_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
done

theorem lwirE: 
  "\<lbrakk> <a, <b#<c#d>>>:lwir(A,B); 
    a:sig(C1); b:sig(C2); c:sig(C3); d:sig(C4);
    \<lbrakk> a=b; c=d \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold lwir_def, erule spreadE)
apply(subgoal_tac "a=b & c=d", simp)
apply(rule)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem rwir_type: "rwir(A,B):A*A*B<~>B"
apply(unfold rwir_def, rule spread_type, blast)
done

theorem rwirR: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> rwir(A,B):A*A*B<R>B"
apply(unfold rwir_def, rule spreadR)
apply(((intro prod_in_chty)?, simp)+)
apply(blast)
done

theorem rwirI: "\<lbrakk> a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <<a#<a#b>>,b>:rwir(A,B)"
apply(unfold rwir_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
done

theorem rwirE: 
  "\<lbrakk> <<a#<b#c>>,d>:rwir(A,B); \<lbrakk> a=b; c=d \<rbrakk> \<Longrightarrow> P;
    a:sig(A'); b:sig(A''); c:sig(B'); d:sig(B'') \<rbrakk> \<Longrightarrow> P"
apply(unfold rwir_def, erule spreadE)
apply(subgoal_tac "a=b & c=d", simp)
apply(rule)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem p1_type: "p1(A,B):A*B<~>A"
apply(unfold p1_def, rule spread_type, blast)
done

theorem p1R: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> p1(A,B):A*B<R>A"
apply(unfold p1_def, rule spreadR)
apply(((intro prod_in_chty)?, simp)+)
apply(blast)
done

theorem p1I: "\<lbrakk> a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <<a#b>, a>:p1(A,B)"
apply(unfold p1_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
done

theorem p1E: 
  "\<lbrakk> <<a#b>,c>:p1(A,B); \<lbrakk> a=c \<rbrakk> \<Longrightarrow> P; 
    a:sig(A'); b:sig(B'); c:sig(A'') \<rbrakk> \<Longrightarrow> P"
apply(unfold p1_def, erule spreadE)
apply(subgoal_tac "a=c", simp)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem p2_type: "p2(A,B):A*B<~>B"
apply(unfold p2_def, rule spread_type, blast)
done

theorem p2R: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> p2(A,B):A*B<R>B"
apply(unfold p2_def, rule spreadR)
apply(((intro prod_in_chty)?, simp)+)
apply(blast)
done

theorem p2I: "\<lbrakk> a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <<a#b>, b>:p2(A,B)"
apply(unfold p2_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
done

theorem p2E: 
  "\<lbrakk> <<a#b>,c>:p2(A,B); \<lbrakk> b=c \<rbrakk> \<Longrightarrow> P; 
    a:sig(A'); b:sig(B'); c:sig(A'') \<rbrakk> \<Longrightarrow> P"
apply(unfold p2_def, erule spreadE)
apply(subgoal_tac "b=c", simp)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem dub_type: "dub(A):A<~>A*A"
apply(unfold dub_def, rule spread_type, blast)
done

theorem dubR: "A:ChTy \<Longrightarrow> dub(A):A<R>A*A"
apply(unfold dub_def, rule spreadR)
apply(((intro prod_in_chty)?, simp)+)
apply(blast)
done

theorem dubI: "a:sig(A) \<Longrightarrow> <a, <a#a>>:dub(A)"
apply(unfold dub_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
done

theorem dubE: 
  "\<lbrakk> <a, <b#c>>:dub(A); \<lbrakk> a=b;a=c \<rbrakk> \<Longrightarrow> P;
    a:sig(A'); b:sig(A''); c:sig(A''') \<rbrakk> \<Longrightarrow> P"
apply(unfold dub_def, erule spreadE)
apply(subgoal_tac "a=b & a=c", simp, rule conjI)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem pzip_type: "pzip(A,B,C,E):(A*B)*C*E<~>(A*C)*B*E"
apply(unfold pzip_def, rule spread_type, blast)
done

theorem pzipR: 
  "\<lbrakk> A:ChTy; B:ChTy; C:ChTy; E:ChTy \<rbrakk>
  \<Longrightarrow> pzip(A,B,C,E):(A*B)*C*E<R>(A*C)*B*E"
apply(unfold pzip_def, rule spreadR)
apply(((intro prod_in_chty)?, simp)+)
apply(blast)
done

theorem pzipI:
  "\<lbrakk> a:sig(A); b:sig(B); c:sig(C); d:sig(E) \<rbrakk>
  \<Longrightarrow> <<<a#b>#<c#d>>,<<a#c>#<b#d>>>:pzip(A,B,C,E)"
apply(unfold pzip_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
done

theorem pzipE:
  "\<lbrakk> <<<a#b>#<c#d>>,<<e#f>#<g#h>>>:pzip(A,B,C,E);
    \<lbrakk> a=e; b=g; c=f; d=h \<rbrakk> \<Longrightarrow> P;
    a:sig(A'); b:sig(B'); c:sig(C'); d:sig(E');
    e:sig(A''); f:sig(C''); g:sig(B''); h:sig(E'') \<rbrakk> \<Longrightarrow> P"
apply(unfold pzip_def, erule spreadE)
apply(subgoal_tac "a=e & b=g & c=f & d=h", simp, intro conjI)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp)+)
done

theorem NNIL_type: "NNIL:nlist[0]A<~>nlist[0]B"
apply(unfold NNIL_def, rule spread_type)
apply(subgoal_tac "nnil:nlist[0]A & nnil:nlist[0]B", simp)
apply(intro conjI nnil_type)
done

theorem NNILR: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> NNIL:nlist[0]A<R>nlist[0]B"
apply(unfold NNIL_def, rule spreadR)
apply((intro nlist_in_chty, simp)+)
apply(subgoal_tac "nnil:nlist[0]A & nnil:nlist[0]B", simp)
apply(intro conjI nnil_type)
done

theorem NNILI: "<snil, snil>:NNIL"
apply(unfold NNIL_def, rule spreadI)
apply(rule, simp add: snil_def)
defer
apply(rule snil_type[of A])
apply(rule snil_type[of B])
apply(subgoal_tac "nnil:nlist[0]A & nnil:nlist[0]B", simp)
apply(intro conjI nnil_type)
done

theorem NNILE: 
  "\<lbrakk> <x,y>:NNIL; x:sig(nlist[0]A'); y:sig(nlist[0]B');
    \<lbrakk> x=snil; y=snil \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold NNIL_def, erule spreadE)
apply(subgoal_tac "x = snil & y = snil", simp, rule conjI)
apply((simp add: snil_def, rule fun_extension, simp+)+)
done

theorem apl_type: "apl(A,n):A*nlist[n]A<~>nlist[succ(n)]A"
apply(unfold apl_def, rule spread_type, blast)
done

theorem aplR: "A:ChTy \<Longrightarrow> apl(A,n):A*nlist[n]A<R>nlist[succ(n)]A"
apply(unfold apl_def, rule spreadR)
apply(((intro prod_in_chty nlist_in_chty)?, simp)+)
apply(blast)
done

theorem aplI: "\<lbrakk> a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> <<a#l>, [a@>l|n]>:apl(A,n)"
apply(unfold apl_def scons_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
apply(insert scons_type, simp add: scons_def)
done

theorem aplE: 
  "\<lbrakk> <<a#la>,[b@>lb|n]>:apl(A,n);
    a:sig(A1); b:sig(A2); la:sig(nlist[n]A3); lb:sig(nlist[n]A4);
    \<lbrakk> a=b; la=lb \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold apl_def scons_def, erule spreadE)
apply(subgoal_tac "a=b & la=lb", simp, intro conjI)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp,
      elim conjE ncons_inject, simp+)+)
done

theorem apr_type: "apr(A,n):nlist[n]A*A<~>nlist[succ(n)]A"
apply(unfold apr_def, rule spread_type, blast)
done

theorem aprR: "A:ChTy \<Longrightarrow> apr(A,n):nlist[n]A*A<R>nlist[succ(n)]A"
apply(unfold apr_def, rule spreadR)
apply(((intro prod_in_chty nlist_in_chty)?, simp)+)
apply(blast)
done

theorem aprI: "\<lbrakk> a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> <<l#a>, [l<@a|n]>:apr(A,n)"
apply(unfold apr_def ssnoc_def)
apply(rule spreadI, rule+)
apply((intro sig_apply_time spair_type, simp+)+)
apply((subst spair_apply_time, simp)+, simp)
apply(blast+)
apply((intro sig_apply_time spair_type, simp+)+)
apply(insert ssnoc_type2, simp add: ssnoc_def)
done

theorem aprE: 
  "\<lbrakk> <<la#a>,[lb<@b|n]>:apr(A,n);
    a:sig(A1); b:sig(A2); la:sig(nlist[n]A3); lb:sig(nlist[n]A4);
    \<lbrakk> a=b; la=lb \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold apr_def ssnoc_def, erule spreadE)
apply(subgoal_tac "a=b & la=lb", simp, intro conjI)
apply((rule fun_extension, simp+,
      drule bspec, simp, 
      (subst (asm) spair_apply_time, simp)+, simp,
      elim conjE nsnoc_inject, simp+)+)
done

lemmas Ruby_type = Ruby_type
  reorg_type cross_type Id_type
  lwir_type rwir_type p1_type p2_type
  dub_type pzip_type NNIL_type
  apl_type apr_type

lemmas RubyR = RubyR
  reorgR crossR IdR lwirR rwirR
  p1R p2R dubR pzipR NNILR
  aplR aprR

lemmas RubyI = RubyI
  reorgI crossI IdI lwirI rwirI
  p1I p2I dubI pzipI NNILI
  aplI aprI

lemmas RubyE = RubyE
  reorgE crossE IdE lwirE rwirE
  p1E p2E dubE pzipE NNILE
  aplE aprE

declare Ruby_type [TC]

end