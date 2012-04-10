Require Export Syntax.
Require Export Arith.
Require Export List.

Open Scope is5_scope.


(* Term variable substitution *)
Reserved Notation " [ M // x ] N " (at level 5).

Fixpoint subst_t M x N :=
match N with
| hyp v => if (eq_nat_dec x v) then M else N
| lam t N' => lam t [M//S x]N'
| appl N' N'' => appl [M//x]N' [M//x]N''
| box N' => box [M//x]N'
| unbox N' => unbox [M//x]N'
| get w N' => get w [M//x]N'
| letd N' N'' => letd [M//x]N' [M//S x]N''
| here N' => here [M//x]N'
| fetch w N' => fetch w [M//x]N'
end
where " [ M // x ] N " := (subst_t M x N) : is5_scope.

(* Substitute L[0] for n, L[1] for n+1,.. in M *)
Fixpoint subst_list L n N :=
match L with
| nil => N
| M :: L' => [M//n] (subst_list L' (S n) N)
end.

(* World variable substitution *)
Reserved Notation " { w1 // w2 } N " (at level 5).

Fixpoint subst_w w1 w2 N :=
match N with
| hyp v => hyp v
| lam t N' => lam t {w1//w2}N'
| appl N' N'' => appl {w1//w2}N' {w1//w2}N''
| box N' => match w1, w2 with
              | fwo w1', bwo w2' => box {w1 // bwo (S w2')}N'
              | fwo w1', fwo w2' => box {w1 // w2} N'
              | bwo w1', bwo w2' => box {bwo (S w1') // bwo (S w2')} N'
              | bwo w1', fwo w2' => box {bwo (S w1')//w2} N'
            end
| unbox N' => unbox {w1//w2}N'
| get w N' => get (if eq_wo_dec w w2 then w1 else w) {w1//w2}N'
| letd N' N'' => match w1, w2 with
                   | fwo w1', bwo w2' => letd {w1 // w2}N' {w1 // bwo (S w2')}N''
                   | fwo w1', fwo w2' => letd {w1 // w2}N' {w1 // w2}N''
                   | bwo w1', bwo w2' => letd {w1//w2}N' {bwo (S w1') // bwo (S w2')} N''
                   | bwo w1', fwo w2' => letd {w1//w2}N' {bwo (S w1')//w2}N''
                 end
| here N' => here {w1//w2}N'
| fetch w N' => fetch (if eq_wo_dec w w2 then w1 else w) {w1//w2}N'
end
where " { w1 // w2 } N " := (subst_w w1 w2 N) : is5_scope.

Definition open_w M w := subst_w w (bwo 0) M.
Notation " M ^ w " := (open_w M w) : is5_scope.

Section Substitution_lemmas.

Lemma no_unbound_worlds_subst_w_id:
forall M w n 
  (H_unbound: unbound_worlds n M = nil),
  {w//bwo n}M = M.
intros;
generalize dependent w;
generalize dependent n;
induction M; intros; simpl in *;
try (rewrite IHM); try auto.
(* appl *)
apply app_eq_nil in H_unbound;
destruct H_unbound;
rewrite IHM1; try rewrite IHM2; auto.
(* box *)
destruct w; try rewrite IHM; auto.
(* get *)
destruct (eq_wo_dec w (bwo n)).
  (* w = bwo n *)
  subst; discriminate.
  (* w <> bwo n *)
  reflexivity.
  destruct w.
    discriminate.
    assumption.
(* letd *)
destruct w;
inversion H_unbound; auto;
apply app_eq_nil in H_unbound;
destruct H_unbound;
rewrite IHM1; try rewrite IHM2; auto.
(* fetch *)
destruct (eq_wo_dec w (bwo n)).
  (* w = bwo n *)
  subst; discriminate.
  (* w <> bwo n *)
  reflexivity.
  destruct w.
    discriminate.
    assumption.
Qed.


Lemma closed_w_subst_id:
forall M w n 
  (HT: lc_w_n M n),
  {w//bwo n} M = M.
intros.
apply no_unbound_worlds_subst_w_id.
apply closed_no_unbound_worlds.
assumption.
Qed.

Lemma subst_order_irrelevant:
forall N M n m w 
  (H_LC: lc_w M),
  {w//bwo m}([M//n]N) = [M//n]({w//bwo m}N).
unfold open_w; intro;
induction N; intros; simpl; try (rewrite IHN; auto).
(* hyp *)
destruct (eq_nat_dec n0 n);
simpl. 
  apply closed_w_subst_id. 
  replace m with (0+m) by auto;
  apply closed_w_addition; assumption.
  reflexivity.
(* appl *)
rewrite IHN1; try rewrite IHN2; auto.
(* box *)
destruct w.
  rewrite IHN; auto.
  simpl; reflexivity.
(* letd *)
destruct w; rewrite IHN1; try rewrite IHN2; auto.
Qed.

Lemma subst_w_comm:
forall M w w' w'' n
  (Neq: w'' <> w),
  {fwo w'//fwo w''}({fwo w//bwo n}M) = {fwo w//bwo n}({fwo w'//fwo w''}M).
induction M; intros; simpl; try (rewrite IHM; auto).
reflexivity.
rewrite IHM1; try rewrite IHM2; auto.
(* get *)
destruct (eq_wo_dec w (bwo n));
destruct (eq_wo_dec w (fwo w''));
destruct (eq_wo_dec (fwo w0) (fwo w''));
destruct (eq_wo_dec w (bwo n));
destruct (eq_wo_dec (fwo w') (bwo n));
subst; 
  try discriminate;
  try (inversion e0; subst; elim Neq; reflexivity);
  try reflexivity.
elim n2; reflexivity.
elim n0; reflexivity.
elim n0; reflexivity.
(* letd *)
rewrite IHM1; try rewrite IHM2; auto. 
(* fetch *)
destruct (eq_wo_dec w (bwo n));
destruct (eq_wo_dec w (fwo w''));
destruct (eq_wo_dec (fwo w0) (fwo w''));
destruct (eq_wo_dec w (bwo n));
destruct (eq_wo_dec (fwo w') (bwo n));
subst; 
  try discriminate;
  try (inversion e0; subst; elim Neq; reflexivity);
  try reflexivity.
elim n2; reflexivity.
elim n0; reflexivity.
elim n0; reflexivity.
Qed.

Lemma subst_id:
forall M w n
  (HT: fresh_world w M),
  {bwo n//fwo w}({fwo w//bwo n}M) = M.
unfold fresh_world;
intros; generalize dependent n;
induction M; intros; simpl in *;
try (rewrite IHM; auto).
reflexivity.
(* appl *)
apply notin_union in HT;
destruct HT;
rewrite IHM1; try rewrite IHM2; auto.
(* get *)
destruct (eq_wo_dec w0 (bwo n)).
destruct (eq_wo_dec (fwo w) (fwo w)).
  subst; reflexivity.
  elim n0; reflexivity.
destruct (eq_wo_dec w0 (fwo w)).
  subst; apply notin_union in HT; destruct HT;
  elim H; rewrite in_singleton; reflexivity.
  reflexivity.
(* ? *)
destruct w0.
  assumption.
  apply notin_union in HT; destruct HT; assumption.
(* letd *)
apply notin_union in HT;
destruct HT;
rewrite IHM1; try rewrite IHM2; auto.
(* fetch *)
destruct (eq_wo_dec w0 (bwo n)).
destruct (eq_wo_dec (fwo w) (fwo w)).
  subst; reflexivity.
  elim n0; reflexivity.
destruct (eq_wo_dec w0 (fwo w)).
  subst; apply notin_union in HT; destruct HT;
  elim H; rewrite in_singleton; reflexivity.
  reflexivity.
(* ? *)
destruct w0.
  assumption.
  apply notin_union in HT; destruct HT; assumption.
Qed.


Lemma subst_neutral:
forall M w w' n
  (HT: lc_w_n M n),
  {fwo w//bwo n}({bwo n//fwo w'}M) = {fwo w//fwo w'}M.
intros. generalize dependent n.
induction M; intros; simpl;
inversion HT; subst.
reflexivity.
rewrite IHM; auto.
rewrite IHM1; try rewrite IHM2; auto.
rewrite IHM; auto.
rewrite IHM; auto.
(* get *)
destruct (eq_wo_dec (fwo w1) (fwo w')).
destruct (eq_wo_dec (bwo n) (bwo n)). 
  rewrite IHM; auto.
  elim n0; reflexivity.
destruct (eq_wo_dec (fwo w1) (bwo n)).
  discriminate.
  rewrite IHM; auto.
rewrite IHM1; try rewrite IHM2; auto.
rewrite IHM; auto.
(* fetch *)
destruct (eq_wo_dec (fwo w1) (fwo w')).
destruct (eq_wo_dec (bwo n) (bwo n)). 
  rewrite IHM; auto.
  elim n0; reflexivity.
destruct (eq_wo_dec (fwo w1) (bwo n)).
  discriminate.
  rewrite IHM; auto.
Qed.

Lemma closed_step_opening:
forall M n w
  (HT: lc_w_n M (S n)),
  lc_w_n ({fwo w//bwo n}M) n.
intros; generalize dependent n; induction M;
intros; inversion HT; subst; simpl;
eauto using lc_w_n.
destruct (eq_wo_dec (fwo w1) (bwo n)); try discriminate;
apply lcw_get; auto.
destruct (eq_wo_dec (fwo w1) (bwo n)); try discriminate;
apply lcw_fetch; auto.
Qed.

End Substitution_lemmas.

Close Scope is5_scope.