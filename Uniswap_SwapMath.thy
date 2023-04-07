theory Uniswap_SwapMath
  imports Uniswap_SqrtPriceMath Uniswap_Tick_Math
begin

definition reserve_change_in_a_step :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<times> real\<close>
  where \<open>reserve_change_in_a_step L price0 price1
    = (L / price1 - L / price0 \<comment> \<open>reserve change in token0\<close>,
       L * (price1 - price0) \<comment> \<open>reserve change in token1\<close>)\<close>

lemma reserve_change_in_a_tick_0:
  \<open>reserve_change_in_a_step L price price = 0\<close>
  unfolding reserve_change_in_a_step_def by (simp add: zero_prod_def)

lemma reserve_change_in_a_tick_sum:
  \<open> price0 \<le> price1 \<and> price1 \<le> price2
\<Longrightarrow> reserve_change_in_a_step L price0 price1 + reserve_change_in_a_step L price1 price2 = reserve_change_in_a_step L price0 price2 \<close>
  unfolding reserve_change_in_a_step_def
  by (simp add: right_diff_distrib)

lemma reserve_change_in_a_tick_sum_rev:
  \<open> price2 \<le> price1 \<and> price1 \<le> price0
\<Longrightarrow> reserve_change_in_a_step L price0 price1 + reserve_change_in_a_step L price1 price2 = reserve_change_in_a_step L price0 price2 \<close>
  unfolding reserve_change_in_a_step_def
  by (simp add: right_diff_distrib)



definition Const_Interval :: \<open>(real \<Rightarrow> 'b) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool\<close> \<comment> \<open>left close, right open\<close>
      \<comment> \<open>An interval where the liquidity is constant\<close>
  where \<open>Const_Interval f l u \<longleftrightarrow> l \<le> u \<and> (\<forall>k. l < k \<and> k < u \<longrightarrow> f k = f l)\<close>

lemma Const_Interval_LE:
  \<open>Const_Interval f l u \<Longrightarrow> l \<le> u\<close>
  unfolding Const_Interval_def by auto

lemma Const_Interval_eq_lower:
  \<open>Const_Interval f l u \<Longrightarrow> l < k \<and> k < u \<Longrightarrow> f k = f l\<close>
  unfolding Const_Interval_def by auto

lemma Const_Interval_triangle:
  \<open>Const_Interval f l m \<Longrightarrow> Const_Interval f l u \<Longrightarrow> m \<le> u \<Longrightarrow> Const_Interval f m u\<close>
  by (smt (verit, del_insts) Const_Interval_def)


primrec Is_partition :: \<open>(real \<Rightarrow> 'b) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> bool\<close>
  where \<open>Is_partition f l u [] \<longleftrightarrow> Const_Interval f l u\<close> |
        \<open>Is_partition f l u (h#r) \<longleftrightarrow> Const_Interval f l h \<and> Is_partition f h u r\<close>

definition KeyPoint
  where \<open>KeyPoint f l k \<longleftrightarrow> Const_Interval f l k \<and> f l \<noteq> f k\<close>

primrec Is_key_partition :: \<open>(real \<Rightarrow> 'b) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> bool\<close>
  where \<open>Is_key_partition f l u [] \<longleftrightarrow> Const_Interval f l u\<close> |
        \<open>Is_key_partition f l u (h#r) \<longleftrightarrow> Const_Interval f l h \<and> KeyPoint f l h \<and> h < u \<and> Is_key_partition f h u r\<close>

lemma KeyPoint_exist:
  \<open>Is_partition f l u ps \<Longrightarrow> \<not> Const_Interval f l u \<Longrightarrow> Ex (KeyPoint f l)\<close>
  apply (induct ps arbitrary: l; simp)
  by (smt (verit, del_insts) Const_Interval_def KeyPoint_def)

lemma xx1:
  \<open>l \<le> u \<Longrightarrow> u \<le> u' \<Longrightarrow> \<not> Const_Interval f l u \<Longrightarrow> \<not> Const_Interval f l u'\<close>
  by (meson Const_Interval_def dual_order.strict_trans1)

lemma KeyPoint_uniq:
  \<open>KeyPoint f l k1 \<Longrightarrow> KeyPoint f l k2 \<Longrightarrow> k1 = k2\<close>
  unfolding KeyPoint_def
  by (smt (verit) Const_Interval_LE Const_Interval_eq_lower) 

lemma KeyPoint_uniq':
  \<open>Const_Interval f l1 l2 \<Longrightarrow> KeyPoint f l1 k1 \<Longrightarrow> KeyPoint f l2 k2 \<Longrightarrow> k1 = k2 \<or> k1 = l2\<close>
  by (smt (verit, ccfv_threshold) Const_Interval_LE Const_Interval_eq_lower KeyPoint_def)

lemma KeyPoint_max:
  \<open>Const_Interval f l u \<Longrightarrow> KeyPoint f l k \<Longrightarrow> u \<le> k\<close>
  by (smt (verit, ccfv_threshold) Const_Interval_LE Const_Interval_eq_lower KeyPoint_def)

lemma Const_Interval_key_point:
  \<open>Const_Interval f l u \<and> KeyPoint f l k \<Longrightarrow> Const_Interval f u k\<close>
  by (smt (verit, best) Const_Interval_def KeyPoint_def)

lemma KeyPoint_in_partition:
  \<open> \<not> Const_Interval f l u
\<Longrightarrow> Is_partition f l u ps
\<Longrightarrow> KeyPoint f l k
\<Longrightarrow> List.member ps k\<close>
  apply (induct ps arbitrary: l; simp add: KeyPoint_def)
  by (smt (verit, best) Const_Interval_def member_rec(1))



(* lemma Is_partition_last[simp]:
  \<open> Is_partition f l ps2
\<Longrightarrow> Is_partition f l (ps2 @ [u]) \<longleftrightarrow> Const_Interval f (last ps2) u\<close>
  by (induct ps2 arbitrary: l; simp) *)

lemma Is_partition_imp_LE:
  \<open>Is_partition f low up ps \<Longrightarrow> low \<le> up\<close>
  apply (induct ps arbitrary: low up; simp)
  apply (simp add: Const_Interval_LE)
  using Const_Interval_LE order_trans by blast

lemma Is_partition_cat:
  \<open> Is_partition f l m ps1
\<Longrightarrow> Is_partition f m u ps2
\<Longrightarrow> Is_partition f l u (ps1 @ [m] @ ps2)\<close>
  by (induct ps1 arbitrary: ps2 m l; simp)
     

lemma Is_partition_ordered_chain:
  \<open>Is_partition f l u ps \<Longrightarrow> \<forall>i < length ps. l \<le> (ps ! i)\<close>
  apply (induct ps arbitrary: l; simp add: Const_Interval_def)
  using less_Suc_eq_0_disj by fastforce

lemma Is_partition_le_last:
  \<open>Is_partition f l u ps \<Longrightarrow> l \<le> u\<close>
  apply (induct ps arbitrary: l; simp add: Const_Interval_def)
  using order_trans by blast


lemma Is_partition_split:
  \<open> Is_partition f l u ps
\<Longrightarrow> List.member ps k
\<Longrightarrow> (\<exists>ps1 ps2. ps = ps1 @ [k] @ ps2 \<and> Is_partition f l k ps1 \<and> Is_partition f k u ps2)\<close>
  apply (induct ps arbitrary: l; simp)
  using member_rec(2) apply force
  by (smt (verit, best) Is_partition.simps(1) Is_partition.simps(2) append_eq_Cons_conv member_rec(1))


lemma Key_partition_exists:
  \<open> Is_partition f l u ps
\<Longrightarrow> Ex (Is_key_partition f l u)\<close>
  apply (induct ps arbitrary: l; simp)
  using Is_key_partition.simps(1) apply blast
  subgoal for a ps l
    apply (cases \<open>KeyPoint f l a\<close>)
     apply (metis Is_key_partition.simps(1) Is_key_partition.simps(2) Is_partition_imp_LE less_eq_real_def)
    apply (cases \<open>Const_Interval f l u\<close>)
      using Is_key_partition.simps(1) apply blast
    subgoal premises prems
    proof -
      have t1: \<open>Is_partition f l u (a # ps)\<close> by (simp add: prems(2))
    obtain kl where kl: \<open>KeyPoint f l kl\<close>
      using KeyPoint_exist prems(4) t1 by blast
    obtain ps' where ps': \<open>Is_key_partition f a u ps'\<close>
      using prems(1) prems(2) by blast
    show ?thesis
    proof (cases ps')
      case Nil
      then show ?thesis
        by (smt (verit, del_insts) Is_key_partition.simps(1) Is_partition_imp_LE KeyPoint_def KeyPoint_max kl prems(2) prems(3) ps' t1 xx1)
    next
      case (Cons a list)
      then show ?thesis
        by (metis Const_Interval_key_point Is_key_partition.simps(2) KeyPoint_def KeyPoint_uniq kl prems(2) prems(3) ps')
    qed
  qed . .

lemma Key_partition_uniq:
  \<open>Is_key_partition f l u ps1 \<Longrightarrow> Is_key_partition f l u ps2 \<Longrightarrow> ps1 = ps2\<close>
  apply (induct ps1 arbitrary: ps2 l u; simp)
  apply (metis Is_key_partition.simps(2) KeyPoint_max linorder_not_le neq_Nil_conv)
  apply (case_tac ps2; simp)
  apply (meson KeyPoint_max less_le_not_le)
  using KeyPoint_uniq by blast

lemma Key_partition_split:
  \<open> Is_key_partition f l u ps
\<Longrightarrow> List.member ps k
\<Longrightarrow> (\<exists>ps1 ps2. ps = ps1 @ [k] @ ps2 \<and> Is_key_partition f l k ps1 \<and> Is_key_partition f k u ps2)\<close>
  apply (induct ps arbitrary: l; simp)
  using member_rec(2) apply force
  apply (auto simp add: member_rec)
   apply (metis Is_key_partition.simps(1) append.left_neutral)
  subgoal premises prems for a ps l proof -
    obtain ps1 ps2 where ps12: \<open>ps = ps1 @ k # ps2 \<and> Is_key_partition f a k ps1 \<and> Is_key_partition f k u ps2\<close>
      using prems(1) prems(5) by presburger
    have t1: \<open>Is_key_partition f l k (a # ps1)\<close> apply simp
      by (metis Const_Interval_LE Is_key_partition.simps(2) KeyPoint_def append_Nil dual_order.order_iff_strict dual_order.strict_trans1 list.inject neq_Nil_conv prems(3) prems(5) ps12)
    show ?thesis
      by (metis append_Cons ps12 t1)
  qed .

(*
lemma
  \<open> Is_partition f l u ps
\<Longrightarrow> Is_key_partition f l u kps
\<Longrightarrow> length kps \<le> length ps\<close>
  apply (induct kps arbitrary: ps l; simp) *)



primrec partition_intergral :: \<open>('b \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a::monoid_add) \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> 'a\<close>
  where \<open>partition_intergral S L low up [] = S (L low) low up\<close> |
        \<open>partition_intergral S L low up (h#l) = S (L low) low h + partition_intergral S L h up l\<close>


lemma partition_intergral_add:
  \<open> (\<forall>C l m u. l \<le> m \<and> m \<le> u \<longrightarrow> S C l m + S C m u = S C l u)
\<Longrightarrow> (\<forall>C a. S C a a = 0)
\<Longrightarrow> Is_partition L l m A
\<Longrightarrow> Is_partition L m u B
\<Longrightarrow> partition_intergral S L l m A + partition_intergral S L m u B = partition_intergral S L l u (A@[m]@B)\<close>
  apply (induct A arbitrary: l; simp)
  by (simp add: add.assoc)
  

lemma partition_intergral_const:
  \<open> (\<forall>C l m u. l \<le> m \<and> m \<le> u \<longrightarrow> S C l m + S C m u = S C l u)
\<Longrightarrow> (\<forall>C a. S C a a = 0)
\<Longrightarrow> Const_Interval L l u
\<Longrightarrow> Is_partition L l u A
\<Longrightarrow> partition_intergral S L l u A = S (L l) l u\<close>
  apply (induct A arbitrary: l; simp)
  by (smt (verit) Const_Interval_def Is_partition_imp_LE)
  

(*
lemma Is_partition_expand:
  \<open>Is_partition L l u (a # list) \<longleftrightarrow> 
      list = [] \<and> a = u \<and> Const_Interval L l u \<or> Is_partition L a u list \<and> Const_Interval L l a\<close>
  unfolding Is_partition_def
  by auto

lemma Is_partition_not_nil:
  \<open>\<not> Is_partition L l u []\<close>
  unfolding Is_partition_def by simp 

term List.member

lemma
  \<open>\<not> Const_Interval L l u \<Longrightarrow> \<exists>k. \<forall>A B. Is_partition L l u A \<and> Is_partition L l u B \<longrightarrow> k\<noteq>u \<and> List.member A k \<and> List.member B k \<close>
  by (metis Is_partition_def in_set_member last_in_set)

lemma
  \<open> Is_partition L l u (A1 @ A2)
\<Longrightarrow> A1 \<noteq> []
\<Longrightarrow> Is_partition L l (last A1) A1 \<and> Is_partition L (last A1) u A2\<close>
  apply (induct )

lemma
  \<open> Is_partition L l u A
\<Longrightarrow> List.member A m
\<Longrightarrow> (\<exists>A1 A2. A1 @ A2 = A \<and> Is_partition L l m A1 \<and> Is_partition L m u A2)\<close>
  

lemma
  \<open>(\<forall>k. \<exists>A B. Is_partition L l u A \<and> Is_partition L l u B \<and> \<not> (List.member A k \<and> List.member B k))
    \<Longrightarrow> Const_Interval L l u\<close>
  apply clarsimp
  by (metis Is_partition_def in_set_member last_in_set)
*)

lemma
  \<open>0 < l \<Longrightarrow> l \<le> u \<Longrightarrow> \<exists>A. Is_partition (L o tick_of_price) l u A\<close>
  subgoal premises prems proof -
    have x1: \<open>tick_of_price l \<le> tick_of_price u\<close>
      by (simp add: prems(1) prems(2) tick_of_price_LE_mono)
    have \<open>\<forall>l'. 0 < l' \<and> l' \<le> u \<longrightarrow> tick_of_price l' = tick_of_price l \<longrightarrow> (\<exists>A. Is_partition (L \<circ> tick_of_price) l' u A)\<close>
      apply (induct rule: int_le_induct[OF x1])
       apply clarify subgoal for l'
         apply (rule exI[where x=\<open>[u]\<close>]; simp add: Is_partition_def Const_Interval_def)
        by (smt (verit, best) tick_of_price_LE_mono)
       apply clarify subgoal premises prems for i l' proof -
        obtain A where A: \<open>Is_partition (L \<circ> tick_of_price) (price_of i) u A\<close>
          by (metis dual_order.order_iff_strict nle_le order_trans prems(1) prems(2) prems(3) prems(4) price_of_L0 price_of_smono price_of_tick tick_of_price)
        have B: \<open>Const_Interval (L \<circ> tick_of_price) l' (price_of i)\<close>
          unfolding Const_Interval_def apply simp
          by (metis diff_add_cancel dual_order.order_iff_strict dual_order.strict_iff_not dual_order.strict_trans2 linorder_linear prems(3) prems(5) price_of_mono price_of_tick tick_of_price_LE_mono zle_diff1_eq)
        show ?thesis
          by (meson B Is_partition.simps(2) \<open>\<And>thesis. (\<And>A. Is_partition (L \<circ> tick_of_price) (price_of i) u A \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
      qed .
    then show ?thesis
      using prems(1) prems(2) by blast
  qed .


lemma partition_intergral_irrelavent_with_parition':
  \<open> (\<forall>C l m u. l \<le> m \<and> m \<le> u \<longrightarrow> S C l m + S C m u = S C l u)
\<Longrightarrow> (\<forall>C a. S C a a = 0)
\<Longrightarrow> Is_partition L l u A
\<Longrightarrow>  partition_intergral S L l u A = partition_intergral S L l u (Eps (Is_key_partition L l u))\<close>
    apply (induct A arbitrary: l; simp)
  apply (metis Is_key_partition.simps(1) Key_partition_uniq partition_intergral.simps(1) someI_ex)
    
    subgoal for a A l
      apply (cases \<open>Const_Interval L l u\<close>)
       apply (smt (verit, best) Const_Interval_LE Const_Interval_eq_lower Const_Interval_triangle Is_key_partition.simps(1) Is_partition_imp_LE Key_partition_uniq partition_intergral.simps(1) someI_ex)
      apply clarify
      subgoal premises prems proof -
        have t1: \<open>Is_partition L l u (a # A)\<close>
          by (simp add: prems(5) prems(6))
        have t2: \<open>Is_key_partition L l u (Eps (Is_key_partition L l u))\<close>
          by (metis Key_partition_exists t1 verit_sko_ex')
        obtain kl where kl: \<open>KeyPoint L l kl\<close>
          using KeyPoint_exist prems(4) t1 by blast
        have t_l_kl: \<open>Const_Interval L l kl\<close>
          using KeyPoint_def kl by blast
        have t3: \<open>List.member (Eps (Is_key_partition L l u)) kl\<close>
          by (metis Is_key_partition.simps(1) Is_key_partition.simps(2) KeyPoint_uniq kl member_rec(1) min_list.cases prems(4) t2)
        obtain ps1 ps2 where ps12: \<open>Eps (Is_key_partition L l u) = ps1 @ [kl] @ ps2 \<and> Is_key_partition L l kl ps1 \<and> Is_key_partition L kl u ps2\<close>
          using Key_partition_split t2 t3 by blast
        have ps12_integral: \<open>partition_intergral S L l u (Eps (Is_key_partition L l u))
                = partition_intergral S L l kl ps1 + partition_intergral S L kl u ps2\<close>
          by (metis (no_types) Is_key_partition.simps(1) Key_partition_uniq append_Cons append_Nil partition_intergral.simps(1) partition_intergral.simps(2) ps12 t_l_kl)
        have ps1_integral: \<open>partition_intergral S L l kl ps1 = S (L l) l kl\<close>
          using Is_key_partition.simps(1) Key_partition_uniq partition_intergral.simps(1) ps12 t_l_kl by blast

        have \<open>KeyPoint L a kl \<or> a = kl\<close>
          by (metis Const_Interval_key_point KeyPoint_def KeyPoint_uniq kl prems(5))
        then consider (a) \<open>a = kl\<close> | (b) \<open>KeyPoint L a kl\<close>
          by blast
        then show ?thesis proof cases
          case a
          then show ?thesis
            by (metis Key_partition_uniq ps12 ps12_integral ps1_integral someI)
        next
          case b
          then show ?thesis
            by (smt (verit) Const_Interval_LE Eps_cong Is_key_partition.simps(1) Is_key_partition.simps(2) Is_partition_imp_LE KeyPoint_def Key_partition_uniq add.assoc append_Cons append_self_conv2 partition_intergral.simps(2) prems(2) prems(4) prems(5) ps12 t1 t_l_kl xx1)
        qed
      qed . .

definition reserve_change_of_partition
  where \<open>reserve_change_of_partition L lower upper ps
    = partition_intergral reserve_change_in_a_step (L o tick_of_price) lower upper ps\<close>

definition reserve_change
  where \<open>reserve_change L lower upper
    = reserve_change_of_partition L lower upper (Eps (Is_key_partition (L o tick_of_price) lower upper))\<close>

lemma reserve_change_irrelavent_with_partition:
  \<open> Is_partition (L o tick_of_price) l u ps
\<Longrightarrow> reserve_change_of_partition L l u ps = reserve_change L l u\<close>
  unfolding reserve_change_of_partition_def reserve_change_def
  by (simp add: partition_intergral_irrelavent_with_parition' reserve_change_in_a_tick_0 reserve_change_in_a_tick_sum)
 



abbreviation XOR (infixr "XOR" 35) where \<open>A XOR B \<equiv> (A \<and> B \<or> \<not> A \<and> \<not> B)\<close>

definition swap_step :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<times> real \<times> real \<times> real\<close>
  \<comment> \<open>As described in the white paper.
      Again we don't consider precision, so the specification can be simple and the difference
        between exactIn and exactOut disappears.
      The module of precision analysis will be designed after completing the \<phi>-system kernel
        and Solidity semantics.\<close>
  where \<open>swap_step price price_target L amount_remain \<gamma> = (
    let zeroForOne = (price >= price_target) ; \<comment> \<open>whether using token0 to buy token1\<close>
        exactIn = amount_remain \<ge> 0 ;
        amount_remain' = if exactIn then amount_remain * (1 - \<gamma>) else amount_remain ;
        max_amount = if zeroForOne XOR exactIn then L / price_target - L / price else L * (price_target - price) ;
        \<Delta>amount = if exactIn then min amount_remain' max_amount else max amount_remain' max_amount ;
        next_price = if L = 0 then price_target else if zeroForOne XOR exactIn then (L / (L / price + \<Delta>amount)) else price + \<Delta>amount / L ;
        amountIn = (if zeroForOne then L / next_price - L / price else L * (next_price - price)) ;
          \<comment> \<open>L / price is the reserve amount of token0, and L * price is that of token 1\<close>
        amountOut = (if zeroForOne then L * (price - next_price) else L / price - L / next_price) ;
        fee = amountIn * \<gamma> / (1 - \<gamma>)
     in (next_price, amountIn, amountOut, fee)
)\<close>

lemma
  \<open> (price >= price_target)
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain \<gamma>
\<Longrightarrow> (amountIn, -amountOut) = reserve_change_in_a_step L price next_price\<close>
  unfolding reserve_change_in_a_step_def swap_step_def
apply (auto simp add: min_def Let_def max_def)
  apply (simp add: minus_mult_right)
  by (metis minus_diff_eq mult_minus_right)

lemma
  \<open> \<not> (price >= price_target)
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain \<gamma>
\<Longrightarrow> (-amountOut, amountIn) = reserve_change_in_a_step L price next_price\<close>
  unfolding reserve_change_in_a_step_def swap_step_def
  by (auto simp add: min_def Let_def max_def)

(* In swap_step, amount_remain cannot be zero *)

(* lemma
  \<open> 0 < price1 \<and> 0 < price_target \<and> 0 < price_target0 \<and> 0 \<le> L \<and> 0 < \<gamma> \<and> \<gamma> < 1
\<Longrightarrow> remain0 \<ge> 0
\<Longrightarrow> price_target0 \<le> price0 \<and> price_target \<le> price_target0
\<Longrightarrow> (price1, amt_in1, amt_out1, fee1) = swap_step price0 price_target0 L remain0 \<gamma>
\<Longrightarrow> (price2, amt_in2, amt_out2, fee2) = swap_step price1 price_target L (remain0 - (amt_in1 + fee1)) \<gamma>
\<Longrightarrow> (price3, amt_in3, amt_out3, fee3) = swap_step price0 price_target L remain0 \<gamma>
\<Longrightarrow> price3 = price2 \<and> amt_in1 + amt_in2 = amt_in3 \<and> amt_out1 + amt_out2 = amt_out3 \<and> fee1 + fee2 = fee3\<close>
  unfolding swap_step_def apply (auto simp add: min_def max_def)
     apply (cases \<open>L = 0\<close>)
      apply (simp add: Let_def)
apply (simp add: Let_def)
*)

declare [[linarith_split_limit = 30]]

lemma swap_step_fee_Le_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 \<le> fee\<close>
  unfolding swap_step_def Let_def
  apply auto
  apply (smt (verit, ccfv_SIG) divide_nonpos_pos frac_le mult.commute mult_less_0_iff pos_divide_le_eq times_divide_eq_left)
  apply (smt (verit, del_insts) divide_cancel_left divide_divide_eq_right divide_nonneg_pos divide_pos_pos eq_divide_imp frac_le less_eq_real_def mult_less_0_iff mult_nonneg_nonneg nonzero_mult_divide_mult_cancel_left2 nonzero_mult_divide_mult_cancel_right nonzero_mult_divide_mult_cancel_right2 not_less_iff_gr_or_eq zero_less_mult_iff)
  by (simp add: frac_le)

lemma price_inequaty:
  \<open>0 < delta \<and> 0 < L \<and> 0 < price \<Longrightarrow> L / (L / price + delta) < price\<close> for L :: real
  by (smt (verit, del_insts) divide_cancel_right divide_pos_pos nonzero_mult_div_cancel_left pos_divide_le_eq)

lemma price_inequaty':
  \<open>0 \<le> delta \<and> 0 < L \<and> 0 < price \<Longrightarrow> L / (L / price + delta) \<le> price\<close> for L :: real
  by (smt (verit) divide_divide_eq_right nonzero_mult_div_cancel_left price_inequaty)

lemma price_inequaty2:
  \<open>0 < L / price + delta \<and> delta < 0 \<and> 0 < L \<and> 0 < price \<Longrightarrow> price < L / (L / price + delta)\<close> for L :: real
  by (smt (verit) mult.commute pos_divide_le_eq)

lemma price_inequaty2':
  \<open>0 < L / price + delta \<and> delta \<le> 0 \<and> 0 < L \<and> 0 < price \<Longrightarrow> price \<le> L / (L / price + delta)\<close> for L :: real
  by (smt (verit) ln_div ln_le_cancel_iff zero_less_divide_iff)
  

lemma swap_step_next_price_Le:
  \<open>0 < min_price \<and> min_price \<le> price \<and> min_price < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> min_price < next_price\<close>
  unfolding swap_step_def Let_def
  apply (cases \<open>price >= price_target\<close>; auto simp add: min_def max_def)
  apply (smt (verit, ccfv_SIG) divide_divide_eq_right mult_eq_0_iff nonzero_mult_div_cancel_left times_divide_eq_left zero_less_mult_iff)
  subgoal premises prems proof -
    have t1: \<open>0 < amount_remain * (1 - feePips)\<close>
      using prems(1) prems(11) prems(14) by fastforce
    thm prems
    have t2: \<open>L / price + amount_remain * (1 - feePips) \<le> L / price_target\<close>
      using prems(12) by force
    have t3: \<open>0 < L / price + amount_remain * (1 - feePips)\<close>
      by (smt (verit, best) divide_nonneg_nonneg prems(2) prems(3) prems(6) prems(9) t1)
    have t4: \<open>price_target \<le> L / (L / price + amount_remain * (1 - feePips))\<close>
      by (metis (no_types, opaque_lifting) divide_pos_pos linorder_linear linorder_not_less mult.commute order_antisym order_less_le_trans pos_le_divide_eq prems(15) prems(9) t2 t3)
    show ?thesis
      using prems(6) t4 by fastforce
  qed
  apply (smt (verit, ccfv_threshold) mult.commute pos_divide_le_eq)
  apply (smt (verit, best) frac_less2 split_mult_neg_le)
     apply (smt (verit) divide_pos_pos mult_pos_pos)
  apply (smt (verit, ccfv_threshold) price_inequaty2 zero_less_divide_iff)
  apply (smt (verit, ccfv_threshold) divide_pos_pos mult_pos_pos)
  by (smt (verit, del_insts) mult_less_0_iff)

lemma swap_step_next_price_Le_MIN_PRICE:
  \<open>MIN_PRICE \<le> price \<and> MIN_PRICE < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> MIN_PRICE < next_price\<close>
  using price_of_L0 swap_step_next_price_Le by blast

lemma swap_step_next_price_Gt:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price \<le> max_price \<and> price_target < max_price
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price < max_price\<close>
  unfolding swap_step_def Let_def
  apply (cases \<open>price >= price_target\<close>; auto simp add: min_def max_def)
  apply (smt (verit, del_insts) mult_nonneg_nonpos)
  apply (smt (verit, del_insts) mult_pos_pos price_inequaty)
  apply (smt (verit, best) divide_neg_pos)
  apply (smt (verit, del_insts) divide_neg_pos)
  apply (smt (verit, best) frac_le)
  apply (metis add.commute diff_less_eq divide_divide_eq_right frac_less2 leI nonzero_mult_div_cancel_left not_less_iff_gr_or_eq order_le_less_trans)
  apply (smt (verit, best) nonzero_mult_div_cancel_left pos_divide_le_eq)
  by (smt (verit, ccfv_SIG) mult_less_0_iff)

lemma swap_step_next_price_Gt_MAX:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price \<le> MAX_PRICE \<and> price_target < MAX_PRICE
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price < MAX_PRICE\<close>
  using swap_step_next_price_Gt .



lemma swap_step_next_price_Le_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 < next_price\<close>
  unfolding swap_step_def Let_def
  apply (auto)
  apply (smt (verit, best) divide_pos_pos mult_nonneg_nonneg)
  apply (smt (verit) mult_nonneg_nonneg zero_le_divide_iff)
  apply (smt (verit) divide_pos_pos)
  by (smt (verit, ccfv_SIG) nonzero_mult_div_cancel_left pos_divide_le_eq)

lemma swap_step_next_price_LE_price:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price_target \<le> price
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price \<le> price\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def)
     apply (smt (verit) divide_divide_eq_right nonzero_mult_div_cancel_left zero_le_mult_iff)
  subgoal premises prems proof -
    have x1: \<open>0 \<le> amount_remain * (1 - feePips)\<close>
      using prems(12) prems(9) by auto
    then show ?thesis
      by (smt (verit, del_insts) divide_eq_0_iff mult.commute pos_divide_le_eq prems(1) prems(3) prems(5))
  qed
  apply (smt (verit) minus_divide_left mult.commute mult_eq_0_iff mult_pos_pos pos_less_minus_divide_eq)
  by (simp add: divide_nonpos_pos)

lemma swap_step_price_target_LE_next_price:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price_target \<le> price
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> price_target \<le> next_price\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def)
  apply (smt (verit) divide_divide_eq_right nonzero_mult_div_cancel_left zero_le_mult_iff)
  subgoal premises prems proof -
    have t1: \<open>0 \<le> amount_remain * (1 - feePips)\<close>
      using prems(12) prems(9) by force
    then show ?thesis
      by (smt (verit, best) divide_pos_pos mult.commute pos_le_divide_eq prems(1) prems(10) prems(13) prems(3) prems(5))
  qed
  apply (smt (verit) mult.commute pos_divide_le_eq)
  by (smt (verit, best) frac_le mult_less_0_iff)

lemma swap_step_price_LE_next_price:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price < price_target
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> price \<le> next_price\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def not_le)
  subgoal premises prems proof -
    have t1: \<open>0 \<le> L / price + amount_remain\<close>
      by (smt (verit, best) divide_nonneg_pos prems(1) prems(10) prems(2) prems(5))
    then show ?thesis
      by (smt (verit, best) divide_le_0_iff mult.commute pos_le_divide_eq prems(1) prems(10) prems(11) prems(2))
  qed .

lemma swap_step_next_price_LE_price_target:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price < price_target
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price \<le> price_target\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def not_le)
  apply (smt (verit, best) frac_less2)
  apply (metis add.commute divide_divide_eq_right dual_order.order_iff_strict frac_less2 less_diff_eq linorder_not_le nonzero_mult_div_cancel_left order_le_less_trans)
  using divide_right_mono apply fastforce
  by (smt (verit, best) mult_less_0_iff)

lemma swap_step_amountIn_Le_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 \<le> amountIn\<close>
  unfolding swap_step_def Let_def
  apply auto
  using frac_le apply blast
  apply (smt (verit) divide_nonpos_pos frac_le mult.commute nonzero_mult_div_cancel_left pos_divide_le_eq)
  apply (auto simp add: min_def max_def not_le)
  by (smt (verit) divide_pos_pos eq_divide_imp frac_less2 mult_divide_mult_cancel_left_if nonzero_mult_divide_mult_cancel_right nonzero_mult_divide_mult_cancel_right2 split_mult_pos_le times_divide_eq_left)

lemma swap_step_amountOut_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 \<le> amountOut\<close>
unfolding swap_step_def Let_def
  apply (clarsimp simp add: max_def min_def)
  apply (simp add: mult_nonneg_nonpos)
  apply (simp add: frac_le)
  apply (auto simp add: not_le)
  apply (smt (verit, del_insts) add_cancel_right_right divide_divide_eq_right mult_le_0_iff mult_not_zero nonzero_mult_div_cancel_left)
  apply (smt (verit, best) mult_le_cancel_left2)
  apply (smt (verit, best) mult_le_cancel_left2)
  subgoal premises prems
  proof -
    have t1: \<open>0 \<le> amount_remain * (1 - feePips)\<close>
      using prems(12) prems(8) by fastforce
    have t2: \<open>L / (L / price + amount_remain * (1 - feePips)) \<le> price\<close>
      by (smt (verit) divide_pos_pos mult.commute pos_divide_le_eq prems(13) prems(14) prems(2) prems(4) t1)
    show ?thesis
      by (simp add: prems(4) t2)
  qed .

proc computeSwapStep:
  input \<open>price \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> price_target \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> L \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amount_remain \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> feePips \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L\<close>
      and  \<open>0 < feePips \<and> feePips < 1\<close>
  output \<open>next_price \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amountIn \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amountOut \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> fee \<Ztypecolon> \<v>\<a>\<l> \<real>
          \<s>\<u>\<b>\<j> next_price amountIn amountOut fee.
          (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips\<close>
  is [routine]
  \<medium_left_bracket>
    var next_price, feeAmount ;;
    \<open>0 \<Ztypecolon> \<real>\<close> \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> var amountIn, amountOut (*TODO: support converge-of-branch between initialized and uninitialized variables*)
    \<open>$price \<ge> $price_target\<close> \<rightarrow> val zeroForOne ;;
    \<open>$amount_remain \<ge> 0\<close> \<rightarrow> val exactIn

    text \<open>We use some local definitions that save us from the very long expressions.\<close>

    define amount_remain' where \<open>amount_remain' = (if ?exactIn then amount_remain * (1 - feePips) else amount_remain)\<close>
    define max_amount where \<open>max_amount =
        (if ?zeroForOne XOR ?exactIn then L / price_target - L / price else L * (price_target - price))\<close>
    define \<Delta>amount where \<open>\<Delta>amount = (if ?exactIn then min amount_remain' max_amount else max amount_remain' max_amount)\<close>
    define next_price where \<open>next_price =
        (if L = 0 then price_target else if ?zeroForOne XOR ?exactIn then (L / (L / price + \<Delta>amount)) else price + \<Delta>amount / L)\<close> 
    define amountIn where \<open>amountIn =
        (if ?zeroForOne then L / next_price - L / price else L * (next_price - price))\<close>
    define amountOut where \<open>amountOut =
        (if ?zeroForOne then L * (price - next_price) else L / price - L / next_price)\<close> ;;

    if \<open>$exactIn\<close> \<medium_left_bracket>
      \<open>$amount_remain * (1 - $feePips)\<close> \<rightarrow> val amountRemainingLessFee ;;
      if \<open>$zeroForOne\<close> \<medium_left_bracket> getAmount0Delta ($price_target, $price, $L) \<medium_right_bracket>.
                       \<medium_left_bracket> getAmount1Delta ($price, $price_target, $L) \<medium_right_bracket>. \<rightarrow> amountIn ;;
      if \<open>$amountRemainingLessFee \<ge> $amountIn\<close> \<medium_left_bracket>
          $price_target \<rightarrow> next_price
      \<medium_right_bracket>. \<medium_left_bracket>
          getNextSqrtPriceFromInput ($price, $L, $amountRemainingLessFee, $zeroForOne)
          affirm using \<phi> by auto (smt (verit, best) divide_cancel_left mult_cancel_left2 zero_le_mult_iff) ;; \<rightarrow> next_price
      \<medium_right_bracket>. is \<open>next_price\<close> 
          affirm using \<phi> by (auto simp add: \<Delta>amount_def max_amount_def amount_remain'_def next_price_def)
    \<medium_right_bracket>. \<medium_left_bracket>
      if \<open>$zeroForOne\<close> \<medium_left_bracket> getAmount1Delta ($price_target, $price, $L) \<medium_right_bracket>.
                       \<medium_left_bracket> getAmount0Delta ($price, $price_target, $L) \<medium_right_bracket>. \<rightarrow> amountOut ;;
      if \<open>-$amount_remain \<ge> $amountOut\<close> \<medium_left_bracket>
          $price_target \<rightarrow> next_price
      \<medium_right_bracket>. \<medium_left_bracket>
          getNextSqrtPriceFromOutput ($price, $L, neg ($amount_remain), $zeroForOne) ;;
            affirm using \<phi> by (auto simp add: not_le) (smt (verit, best) divide_cancel_left left_diff_distrib) ;;
            affirm using \<phi> by (auto simp add: not_le)  (smt (verit, best) \<open>0 < price \<and> 0 < L\<close> mult.commute pos_less_minus_divide_eq)
          ;; \<rightarrow> next_price
      \<medium_right_bracket>. is \<open>next_price\<close>
          affirm using \<phi> apply (auto simp add: not_le \<Delta>amount_def max_amount_def amount_remain'_def next_price_def)
                          apply (smt (verit, best) mult_minus_right nonzero_mult_div_cancel_left)
                          apply (smt (verit, best) mult_minus_right)
                          apply (smt (verit, best) frac_le)
                          by (metis max.absorb3 minus_diff_eq minus_less_iff mult_minus_right)
    \<medium_right_bracket>. ;;

    \<open>$price_target = $next_price\<close> \<rightarrow> val max ;;

    text \<open>Now we claim two intermediate lemmas that will help the later construction.\<close>

    have t1[simp]: \<open>?zeroForOne \<Longrightarrow> price_target \<le> next_price \<and> next_price \<le> price\<close>
      unfolding \<Delta>amount_def max_amount_def amount_remain'_def next_price_def
      using \<phi> apply (auto simp add: min_def max_def not_le)
      apply (smt (verit) divide_pos_pos mult.commute mult_nonneg_nonneg pos_le_divide_eq)
      apply (metis diff_ge_0_iff_ge diff_self divide_divide_eq_right linorder_not_less mult_pos_neg mult_zero_left mult_zero_right nat_arith.rule0 nonzero_mult_div_cancel_left order_antisym order_trans)
      apply (smt (verit, del_insts) divide_pos_pos mult.commute pos_le_divide_eq split_mult_pos_le)
      apply (smt (verit, ccfv_threshold) divide_pos_pos mult.commute mult_nonneg_nonneg pos_divide_le_eq)
      apply (smt (verit, ccfv_SIG) mult.commute pos_le_divide_eq)
      apply (simp add: divide_nonpos_pos)
      apply (smt (verit, ccfv_SIG) divide_le_cancel nonzero_mult_div_cancel_left)
      by (simp add: divide_nonpos_pos)

    have t2[simp]: \<open>\<not> ?zeroForOne \<Longrightarrow> price \<le> next_price \<and> next_price \<le> price_target\<close>
      unfolding \<Delta>amount_def max_amount_def amount_remain'_def next_price_def
      using \<phi> apply (auto simp add: min_def max_def not_le)
      apply (smt (verit, ccfv_SIG) frac_less2)
      apply (smt (verit, del_insts) divide_divide_eq_right divide_pos_pos frac_le linorder_not_less nonzero_mult_div_cancel_left)
      apply (smt (verit, del_insts) divide_pos_pos mult.commute pos_divide_le_eq)
      using divide_right_mono apply fastforce
      apply (smt (verit, best) mult_less_0_iff)
      by (smt (verit, best) mult_less_0_iff) ;;

    if \<open>$zeroForOne\<close>
       \<medium_left_bracket>
      if \<open>$max \<and> $exactIn\<close> \<medium_left_bracket> $amountIn \<medium_right_bracket>. \<medium_left_bracket>
        getAmount0Delta ($next_price, $price, $L) affirm using \<phi> t1 by (auto; linarith) ;; \<medium_right_bracket>.
      \<rightarrow> amountIn is amountIn affirm unfolding amountIn_def using \<phi> by auto ;;
      if \<open>$max \<and> \<not> $exactIn\<close> \<medium_left_bracket> $amountOut \<medium_right_bracket>. \<medium_left_bracket>
        getAmount1Delta ($next_price, $price, $L) affirm using \<phi> t1 by (auto; linarith) ;; \<medium_right_bracket>.
      \<rightarrow> amountOut is amountOut affirm unfolding amountOut_def using \<phi> by auto
    \<medium_right_bracket>. \<medium_left_bracket>
      if \<open>$max \<and> $exactIn\<close> \<medium_left_bracket> $amountIn \<medium_right_bracket>. \<medium_left_bracket>
        getAmount1Delta ($price, $next_price, $L) \<medium_right_bracket>.
      \<rightarrow> amountIn is amountIn affirm unfolding amountIn_def using \<phi> by auto ;;
      if \<open>$max \<and> \<not> $exactIn\<close> \<medium_left_bracket> $amountOut \<medium_right_bracket>. \<medium_left_bracket>
        getAmount0Delta ($price, $next_price, $L) \<medium_right_bracket>.
      \<rightarrow> amountOut is amountOut affirm unfolding amountOut_def using \<phi> by auto
    \<medium_right_bracket>. ;;
  
  have t3: \<open>\<not> ?exactIn \<Longrightarrow> amountOut \<le> - amount_remain\<close>
    unfolding amountOut_def next_price_def \<Delta>amount_def amount_remain'_def max_amount_def
    using \<phi> by auto
  text \<open>Therefore, when there is no precision lost, the following branch will never be entered\<close> ;;

  if \<open>\<not> $exactIn \<and> $amountOut > - $amount_remain\<close> \<medium_left_bracket>
    \<open>- $amount_remain\<close> \<rightarrow> amountOut
  \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. is amountOut affirm using t3 by auto ;;

  if \<open>$exactIn \<and> $next_price \<noteq> $price_target\<close> \<medium_left_bracket>
    \<open>$amount_remain - $amountIn\<close> \<rightarrow> feeAmount is \<open>amountIn * feePips / (1 - feePips)\<close>
    affirm using \<phi> by (auto simp add: amountIn_def next_price_def \<Delta>amount_def amount_remain'_def max_amount_def min_def;
                       simp add: right_diff_distrib' right_diff_distrib)
  \<medium_right_bracket>. \<medium_left_bracket> \<open>$amountIn * $feePips / (1 - $feePips)\<close> \<rightarrow> feeAmount \<medium_right_bracket>. ;;

  return ($next_price, $amountIn, $amountOut, $feeAmount)
    affirm using \<phi> by (auto simp add: swap_step_def Let_def amountIn_def next_price_def \<Delta>amount_def
                                      amount_remain'_def max_amount_def amountOut_def)
  \<medium_right_bracket>. .

end