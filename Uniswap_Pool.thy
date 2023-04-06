theory Uniswap_Pool
  imports Uniswap_SwapMath Uniswap_Tick_Math UniSWP_TickBitmap UniSWP_Tick
begin

no_notation Reals ("\<real>") (*TODO: use that patch!*)

type_synonym fee_protocal = \<open>nat \<times> nat\<close>

datatype pool = pool (price: real) (tick: int) (unlocked: bool) (liquidity: real)
                     (fee_growth_0: real) (fee_growth_1: real) (fee_protocal: fee_protocal)

hide_const (open) price tick unlocked liquidity fee_growth_0 fee_growth_1 fee_protocal

setup \<open>Sign.mandatory_path "pool"\<close>

definition \<open>map_price f x = (case x of pool p t u l f1 f2 fp \<Rightarrow> pool (f p) t u l f1 f2 fp)\<close>
lemma map_price[simp]:
  \<open>pool.map_price f (pool p t u l f1 f2 fp) = pool (f p) t u l f1 f2 fp\<close>
  unfolding pool.map_price_def by simp

definition \<open>map_tick f x = (case x of pool p t u l f1 f2 fp \<Rightarrow> pool p (f t) u l f1 f2 fp)\<close>
lemma map_tick[simp]:
  \<open>pool.map_tick f (pool p t u l f1 f2 fp) = pool p (f t) u l f1 f2 fp\<close>
  unfolding pool.map_tick_def by simp

definition \<open>map_unlock f x = (case x of pool p t u l f1 f2 fp \<Rightarrow> pool p t (f u) l f1 f2 fp)\<close>
lemma map_unlock[simp]:
  \<open>pool.map_unlock f (pool p t u l f1 f2 fp) = pool p t (f u) l f1 f2 fp\<close>
  unfolding pool.map_unlock_def by simp

definition \<open>map_liquidity f x = (case x of pool p t u l f1 f2 fp \<Rightarrow> pool p t u (f l) f1 f2 fp)\<close>
lemma map_liquidity[simp]:
  \<open>pool.map_liquidity f (pool p t u l f1 f2 fp) = pool p t u (f l) f1 f2 fp\<close>
  unfolding pool.map_liquidity_def by simp

definition \<open>map_fee_growth_0 f x = (case x of pool p t u l f1 f2 fp \<Rightarrow> pool p t u l (f f1) f2 fp)\<close>
lemma fee_growth_0[simp]:
  \<open>pool.map_fee_growth_0 f (pool p t u l f1 f2 fp) = pool p t u l (f f1) f2 fp\<close>
  unfolding pool.map_fee_growth_0_def by simp

definition \<open>map_fee_growth_1 f x = (case x of pool p t u l f1 f2 fp \<Rightarrow> pool p t u l f1 (f f2) fp)\<close>
lemma map_fee_growth_1[simp]:
  \<open>pool.map_fee_growth_1 f (pool p t u l f1 f2 fp) = pool p t u l f1 (f f2) fp\<close>
  unfolding pool.map_fee_growth_1_def by simp

definition \<open>map_fee_protocal f x = (case x of pool p t u l f1 f2 fp \<Rightarrow> pool p t u l f1 f2 (f fp))\<close>
lemma map_fee_protocal[simp]:
  \<open>pool.map_fee_protocal f (pool p t u l f1 f2 fp) = pool p t u l f1 f2 (f fp)\<close>
  unfolding pool.map_fee_protocal_def by simp

setup \<open>Sign.parent_path\<close>


consts fee :: real \<comment> \<open>We model the fee by a constant now\<close>
specification (fee)
  fee_range[simp]: \<open>0 < fee \<and> fee < 1\<close>
  by (simp add: dense)
  

lemma [\<phi>reason 1000]: \<open> Is_Literal fee\<close> unfolding Is_Literal_def ..

proc (nodef) fee[\<phi>synthesis 1100]:
  input \<open>Void\<close>
  output \<open>fee \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  \<medium_left_bracket> op_const_areal[where x=fee] \<medium_right_bracket>. .


locale Pool = Tickmap_spec + Tick_spec +
  fixes Pool :: \<open>(fiction, pool) \<phi>\<close>
    and op_get_pool_price :: \<open>VAL proc\<close>
    and op_set_pool_price :: \<open>(VAL,unit) proc'\<close>
    and op_get_pool_tick :: \<open>VAL proc\<close>
    and op_set_pool_tick :: \<open>(VAL,unit) proc'\<close>
    and op_get_pool_unlock :: \<open>VAL proc\<close>
    and op_set_pool_unlock :: \<open>(VAL,unit) proc'\<close>
    and op_get_liquidity :: \<open>VAL proc\<close>
    and op_set_liquidity :: \<open>(VAL,unit) proc'\<close>
    and op_get_fee_growth_0 :: \<open>VAL proc\<close>
    and op_set_fee_growth_0 :: \<open>(VAL,unit) proc'\<close>
    and op_get_fee_growth_1 :: \<open>VAL proc\<close>
    and op_set_fee_growth_1 :: \<open>(VAL,unit) proc'\<close>
    and op_get_fee_protocal_0 :: \<open>VAL proc\<close>
    and op_get_fee_protocal_1 :: \<open>VAL proc\<close>
  assumes [\<phi>inhabitance_rule]:
    \<open>s \<Ztypecolon> Pool \<i>\<m>\<p>\<l>\<i>\<e>\<s> UNIV \<a>\<n>\<d> 0 < pool.price s \<and> pool.tick s \<in> {MIN_TICK..MAX_TICK}\<close>
  and get_pool_price_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_pool_price \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.price s \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_price_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_pool_price rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> p' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_price (\<lambda>_. p') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_tick_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_pool_tick \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.tick s \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace> \<close>
  and set_pool_tick_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_pool_tick ri \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> t' \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<longmapsto> pool.map_tick (\<lambda>_. t') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_unlock_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_get_pool_unlock \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.unlocked s \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>
  and set_pool_unlock_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_pool_unlock rb \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> b' \<Ztypecolon> \<v>\<a>\<l>[rb] \<bool> \<longmapsto> pool.map_unlock (\<lambda>_. b') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_liquidity_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_liquidity \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.liquidity s \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_liquidity_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_liquidity rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> l' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_liquidity (\<lambda>_. l') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_fee_growth_0_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_growth_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.fee_growth_0 s \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_fee_growth_0_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_fee_growth_0 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_fee_growth_0 (\<lambda>_. c') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_fee_growth_1_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_growth_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.fee_growth_1 s \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_fee_growth_1_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_fee_growth_1 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_fee_growth_1 (\<lambda>_. c') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_fee_protocal_0[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_protocal_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> fst (pool.fee_protocal s) \<Ztypecolon> \<v>\<a>\<l> \<nat> \<rbrace> \<close>
  and get_fee_protocal_1[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_protocal_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> snd (pool.fee_protocal s) \<Ztypecolon> \<v>\<a>\<l> \<nat> \<rbrace> \<close>


begin

term growth.fee0

definition Uniswap_Pool :: \<open>(fiction, real \<times> tick \<times> bool \<times> liquidity \<times> liquidity \<times> growths \<times> opt_growths \<times> fee_protocal) \<phi>\<close>
  where [\<phi>defs]: \<open>Uniswap_Pool x = (
    case x of (price, i, unlocked, Lg, L, growth, \<delta>, fee_proto) \<Rightarrow>
        \<comment> \<open>\<open>growth\<close> is the abstract growth happened on every tick\<close>
      pool price i unlocked (L i) (growth.fee0 (gSum growth)) (growth.fee1 (gSum growth)) fee_proto \<Ztypecolon> Pool\<heavy_comma>
        \<comment> \<open>so the global fee growth is the sum of the \<open>growth\<close> over every tick\<close>
      (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
        \<comment> \<open>\<open>k \<in> dom \<delta>\<close> means the tick \<open>k\<close> is initialized\<close>
      (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks
    \<s>\<u>\<b>\<j> tick_of_price price = i
)\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 1200]:
  \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_proto) \<Ztypecolon> Uniswap_Pool \<i>\<m>\<p>\<l>\<i>\<e>\<s>
   pool price i unlocked (L i) (growth.fee0 (gSum growth)) (growth.fee1 (gSum growth)) fee_proto \<Ztypecolon> Pool\<heavy_comma>
   (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
   (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks
  \<a>\<n>\<d> tick_of_price price = i
  @action to RAW\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> tick_of_price price = i
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> pool price i unlocked (L i) (growth.fee0 (gSum growth)) (growth.fee1 (gSum growth)) fee_proto \<Ztypecolon> Pool\<heavy_comma>
        (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
        (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (price, i, unlocked, Lg, L, growth, \<delta>, fee_proto) \<Ztypecolon> Uniswap_Pool \<a>\<n>\<d> P\<close>
  \<medium_left_bracket> premises _ and I
    I construct\<phi> \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_proto) \<Ztypecolon> Uniswap_Pool\<close> \<medium_right_bracket>. .

declare Invt_Ticks_def[simp] Invt_A_Tick_def[simp]

(*
definition swap_loop_transition :: \<open>bool \<Rightarrow> bool \<Rightarrow> nat \<times> nat \<Rightarrow> liquidity \<Rightarrow> tick \<times> fee \<Rightarrow> unit\<close>
  where \<open>swap_loop_transition exactIn zeroForOne fee_protocal L
    =(\<lambda>(j,ar).
      let fee_proto = (if zeroForOne then fst fee_protocal else snd fee_protocal) ;
          (next_price, amountIn, amountOut, fee_amount) =
  swap_step pr (if zeroForOne then max (price_of tick_next) price_limit else min (price_of tick_next) price_limit) (L j) ar fee
       in ())\<close> *)

proc swap:
  input \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_protocal) \<Ztypecolon> Uniswap_Pool\<heavy_comma>
         recipient \<Ztypecolon> \<v>\<a>\<l> Address\<heavy_comma> zeroForOne \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> amount_specified \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> price_limit \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 \<noteq> amount_specified \<and> 0 < price_limit\<close> and \<open>unlocked\<close>
      and \<open>if zeroForOne then price_limit < price \<and> price_limit > MIN_PRICE
                         else price_limit > price \<and> price_limit < MAX_PRICE\<close>
    (*soon we will have exception-based require statement*)
  output \<open>amount0 \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amount1 \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  (* is [noDelegateCall]  Currently no modifier is supported, but is planned *)
  \<medium_left_bracket> D ;;
    require (\<open>$amount_specified \<noteq> 0\<close>) ;;
    require (get_pool_unlock) ;;
    require (
      sel ( \<open>$price_limit < (pool.price _) \<and> $price_limit > MIN_PRICE\<close>,
            \<open>$price_limit > (pool.price _) \<and> $price_limit < MAX_PRICE\<close>,
            $zeroForOne)) ;;
    set_pool_unlock (\<open>False\<close>)  ;;

    have w1: \<open>\<not> zeroForOne \<Longrightarrow> price < MAX_PRICE\<close>
      using the_\<phi>(15) by fastforce
    have w2: \<open>\<not> zeroForOne \<Longrightarrow> i < MAX_TICK\<close>
      apply (simp add: \<open>tick_of_price price = i\<close>[symmetric])
      using less_MAX_PRICE_less_MAX_TICK
      using pool.sel(1) the_\<phi>(1) w1 by presburger

    define fee_proto where \<open>fee_proto = (if zeroForOne then fst fee_protocal else snd fee_protocal)\<close> ;;

    \<open>pool.liquidity _\<close> \<rightarrow> val liquidityStart
    sel (\<open>fst (pool.fee_protocal _)\<close> \<open>snd (pool.fee_protocal _)\<close> $zeroForOne)
        is fee_proto affirm unfolding fee_proto_def by simp ;; \<rightarrow> val feeProtocol
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> val secondsPerLiquidityCumulative
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> val tickCumulative

    (* no blockTimestamp because we don't cover observation *)

    \<open>$amount_specified > 0\<close> \<rightarrow> val exactInput

    define I_fee_growth_global where
      \<open>\<And>gr. I_fee_growth_global gr = (if zeroForOne then global_fee0_growth gr else global_fee1_growth gr)\<close> ;;

    $amount_specified, \<open>0 \<Ztypecolon> \<real>\<close>,
      \<open>pool.price _\<close>, \<open>pool.tick _\<close>,
      sel (\<open>pool.fee_growth_0 _\<close> \<open>pool.fee_growth_1 _\<close> $zeroForOne)
          is \<open>I_fee_growth_global growth\<close> affirm unfolding I_fee_growth_global_def by simp ;;
      \<open>0 \<Ztypecolon> \<real>\<close>, $liquidityStart
    \<rightarrow> var amount_reamining, amount_calculated, price, tick, fee_growth_global, protocolFee, liquidity ;;

    while \<open>ar \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_amount_reamining] \<real>\<heavy_comma>
           pr \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_price] \<real>\<heavy_comma>
           ac \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_amount_calculated] \<real>\<heavy_comma>
           pf \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_protocolFee] \<real>\<heavy_comma>
            j \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_tick] Tick\<heavy_comma>
           L j \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] \<real>\<heavy_comma>
          I_fee_growth_global growth' \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_fee_growth_global] \<real>\<heavy_comma>
          (Lg, L, growth', j, \<delta>) \<Ztypecolon> Ticks
        \<s>\<u>\<b>\<j> ar pr ac pf j growth' f\<^sub>\<Delta> .
            Inv: ( MIN_PRICE \<le> pr \<and> pr < MAX_PRICE
                 \<and> j < MAX_TICK
                 \<and> tick_of_price pr = j
                 \<and> (if zeroForOne then price_limit \<le> pr else pr \<le> price_limit)
                 \<and> (if zeroForOne then growth.fee1 o growth' = growth.fee1 o growth
                                  else growth.fee0 o growth' = growth.fee0 o growth))
          \<and> Guard: (ar \<noteq> 0 \<and> pr \<noteq> price_limit)\<close>
    \<medium_left_bracket> \<open>$amount_reamining \<noteq> 0 \<and> $price \<noteq> $price_limit\<close> \<medium_right_bracket>.
    \<medium_left_bracket>
      $price \<rightarrow> val step_price_start ;;
      nextInitializedTickWithinOneWord ($tick, $zeroForOne) \<exists>tick_next' \<rightarrow> var tick_next, val initialized ;;

      define tick_next where \<open>tick_next = max MIN_TICK (min MAX_TICK tick_next')\<close> ;;

      if \<open>$tick_next < MIN_TICK\<close> \<medium_left_bracket> \<open>MIN_TICK\<close> \<rightarrow> tick_next \<medium_right_bracket>. \<medium_left_bracket>
        if \<open>$tick_next > MAX_TICK\<close> \<medium_left_bracket> \<open>MAX_TICK\<close> \<rightarrow> tick_next \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;
      \<medium_right_bracket>. as \<open>tick_next \<Ztypecolon> Tick\<close> affirm unfolding tick_next_def using \<phi> by auto ;;

      have t0[useful]: \<open>0 < pr\<close> by (smt (verit, best) price_of_L0 the_\<phi>(21))

      have t2: \<open>0 < Lg tick_next' \<Longrightarrow> 0 < Lg tick_next\<close>
        using \<phi> by (clarsimp, metis \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> the_\<phi>(16) verit_comp_simplify1(3))

      have tick_next_dom: \<open>MIN_TICK \<le> tick_next\<close> \<open>tick_next \<le> MAX_TICK\<close>
        using the_\<phi>(4) apply force
        using the_\<phi>(5) by blast

      have y0: \<open>if j < tick_next' then next_initialized Lg j tick_next' else next_initialized Lg (tick_next') (j+1)\<close>
        by (auto,
            metis dual_order.strict_trans1 greaterThanLessThan_iff not_less_iff_gr_or_eq the_\<phi>(13) the_\<phi>lemmata(3),
            metis greaterThanAtMost_iff less_eq_real_def order.strict_trans2 order_less_imp_not_less the_\<phi>(13) the_\<phi>lemmata(3))
      
      have y1: \<open>if j < tick_next then next_initialized Lg j tick_next else next_initialized Lg tick_next (j+1)\<close>
        using \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> the_\<phi>(6) the_\<phi>(7) y0 by fastforce

      have x1: \<open>zeroForOne \<Longrightarrow> tick_next \<le> j\<close>
        using the_\<phi>(6) the_\<phi>lemmata(3) tick_next_def by fastforce

      have x1': \<open>\<not> zeroForOne \<Longrightarrow> j < tick_next\<close>
        using \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> the_\<phi>(21) the_\<phi>lemmata(3) by fastforce

      have t8: \<open>zeroForOne \<Longrightarrow> \<forall>k. tick_next < k \<and> k \<le> j \<longrightarrow> Lg k = 0\<close>
        using y1 by force

      have t8': \<open>\<not> zeroForOne \<Longrightarrow> \<forall>k. j < k \<and> k < tick_next \<longrightarrow> Lg k = 0\<close>
        using y1 by force

      have t8': \<open>\<not> zeroForOne \<Longrightarrow> \<forall>k. j < k \<and> k \<le> (tick_next - 1) \<longrightarrow> Lg k = 0\<close>
        using y1 by force

      have t7: \<open>\<And>k. zeroForOne \<Longrightarrow> tick_next \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> L k = L j\<close>
        subgoal premises Ps for k
          using t8 Ps(2) apply (induct rule: int_le_induct[where k=j and i=k, OF Ps(3)]; simp)
          by (metis Ps(1) the_\<phi>(12)) .

      have t11: \<open>\<And>k. \<not> zeroForOne \<Longrightarrow> k < tick_next \<Longrightarrow> j \<le> k \<Longrightarrow> L k = L j\<close>
        subgoal premises Ps for k
          using t8' Ps(2) apply (induct rule: int_ge_induct[where k=j and i=\<open>k\<close>, OF Ps(3)]; simp)
          by (simp add: Ps(1) the_\<phi>(12)) .
      ;;

      getSqrtRatioAtTick ($tick_next) \<rightarrow> val step_price_next ;;

      computeSwapStep (
        $price,
        sel ($price_limit, $step_price_next,
                sel (\<open>$step_price_next < $price_limit\<close>, \<open>$step_price_next > $price_limit\<close>, $zeroForOne))
         is \<open>if zeroForOne then max ?step_price_next price_limit else min ?step_price_next price_limit\<close>,
        $liquidity,
        $amount_reamining,
        fee) \<exists>next_price, amountIn, amountOut, fee_amount
     \<rightarrow> val amountIn, amountOut, feeAmount \<rightarrow> price ;;
     (*FIX ME: ^ there is a bug*)
      thm \<phi>
      have t1[simp]: \<open>L j = 0 \<Longrightarrow> fee_amount = 0\<close>
        using \<open>_ = swap_step _ _ _ _ _\<close> by (auto simp add: swap_step_def Let_def)

      have kk1: \<open>MIN_PRICE < (if zeroForOne then max ?step_price_next price_limit else min ?step_price_next price_limit)\<close>
        by (smt (verit, del_insts) price_of_smono price_of_tick the_\<phi>(19) the_\<phi>(3) the_\<phi>(6) the_\<phi>(9) the_\<phi>lemmata(1) x1')

      have kk3: \<open>\<not> zeroForOne \<Longrightarrow> min ?step_price_next price_limit < MAX_PRICE\<close>
        using the_\<phi>(19) by force

      have kk2: \<open>MIN_PRICE < next_price\<close>
        using fee_range kk1 swap_step_next_price_Le_MIN_PRICE the_\<phi>(14) the_\<phi>(21) the_\<phi>(22) the_\<phi>lemmata(4) by blast

      have kk4: \<open>\<not> zeroForOne \<Longrightarrow> next_price < MAX_PRICE\<close>
        by (smt (verit, ccfv_SIG) fee_range kk1 kk3 price_of_L0 swap_step_next_price_Gt_MAX the_\<phi>(14) the_\<phi>(21) the_\<phi>(22) the_\<phi>lemmata(4))

      have kk8: \<open>zeroForOne \<Longrightarrow> next_price \<le> pr\<close>
        by (smt (verit, best) fee_range price_of_L0 price_of_smono price_of_tick swap_step_next_price_LE_price the_\<phi>(14) the_\<phi>(21) the_\<phi>lemmata(4) x1)

      have kk6: \<open>zeroForOne \<Longrightarrow> price_of tick_next \<le> next_price \<and> price_limit \<le> next_price\<close>
        by (smt (verit, ccfv_threshold) fee_range kk8 swap_step_next_price_Le swap_step_next_price_Le_0 t0 the_\<phi>(14) the_\<phi>(17) the_\<phi>(22) the_\<phi>lemmata(4))

      have kk9: \<open>\<not> zeroForOne \<Longrightarrow> pr \<le> next_price\<close>
        by (smt (verit, best) fee_range price_of_L0 price_of_smono price_of_tick swap_step_next_price_Le the_\<phi>(14) the_\<phi>(21) the_\<phi>(22) the_\<phi>lemmata(4) x1')

      have kk7: \<open>\<not> zeroForOne \<Longrightarrow> next_price \<le> price_of tick_next \<and> next_price \<le> price_limit\<close>
        subgoal premises P
        apply (rule swap_step_next_price_LE_price_target[OF _ _ \<open>_ = swap_step _ _ _ _ _\<close>, simplified P, simplified])
          using t0 the_\<phi>(14) the_\<phi>(17) apply blast
          by (smt (verit, best) P price_of_smono price_of_tick t0 the_\<phi>(21) the_\<phi>(22) x1') .

      ;;


      if \<open>$exactInput\<close> \<medium_left_bracket>
          \<open>$amount_reamining - ($amountIn + $feeAmount)\<close> \<rightarrow> amount_reamining
          \<open>$amount_calculated - $amountOut\<close> \<rightarrow> amount_calculated
      \<medium_right_bracket>. \<medium_left_bracket>
          \<open>$amount_reamining + $amountOut\<close> \<rightarrow> amount_reamining
          \<open>$amount_calculated + ($amountIn + $feeAmount)\<close> \<rightarrow> amount_calculated
      \<medium_right_bracket>. ;;

      if \<open>$feeProtocol > 0\<close> \<medium_left_bracket>
        \<open>$feeAmount / real $feeProtocol\<close> \<rightarrow> val delta
        \<open>$feeAmount - $delta\<close> \<rightarrow> feeAmount
        \<open>$protocolFee + $delta\<close> \<rightarrow> protocolFee
      \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;

      define growth'' where \<open>
          growth'' = growth'(j := growth' j + (if L j = 0 then 0
                        else if zeroForOne then (fee_amount / L j, 0) else (0, fee_amount / L j)))\<close> ;;

      grow_current_tick[where \<Delta>=\<open>if L j = 0 then 0 else if zeroForOne then (fee_amount / L j,0) else (0, fee_amount / L j)\<close>]
        affirm using \<phi> by (auto simp add: zero_prod_def less_eq_prod_def)
                          (smt (verit, best) divide_nonneg_nonneg fee_range price_of_L0 swap_step_fee_Le_0) ;;
        is \<open>(Lg, L, growth'', _, _)\<close> affirm unfolding growth''_def by simp ;;

      if \<open>$liquidity > 0\<close> \<medium_left_bracket>
        \<open>$fee_growth_global + ($feeAmount / $liquidity)\<close> \<rightarrow> fee_growth_global
        (*TODO: \<open>fee_growth_0\<close> give interesting result?*)
      \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
      is \<open>I_fee_growth_global growth''\<close>
      affirm unfolding I_fee_growth_global_def growth''_def
              using \<phi> by (auto simp add: fun_eq_iff) (meson linorder_not_le nle_le) ;;
              
      define real_next_tick where \<open>real_next_tick = (if zeroForOne then tick_next - 1 else tick_next)\<close> 

      have real_next_tick_dom[simp]: \<open>real_next_tick \<in> {MIN_TICK - 1..MAX_TICK}\<close>
        using real_next_tick_def tick_next_dom(1) tick_next_dom(2) by fastforce ;;

      if \<open>$price = $step_price_next\<close> \<medium_left_bracket>

        if \<open>$initialized\<close> \<medium_left_bracket>

           $tick_next,

           sel ($fee_growth_global, \<open>pool.fee_growth_0 _\<close>, $zeroForOne)
              is \<open>global_fee0_growth growth''\<close>
            affirm unfolding I_fee_growth_global_def growth''_def using \<phi> by (clarsimp; metis fee0_sum) ;;

           sel (\<open>pool.fee_growth_1 _\<close>, $fee_growth_global, $zeroForOne)
              is \<open>global_fee1_growth growth''\<close>
              affirm unfolding I_fee_growth_global_def growth''_def using \<phi> by (clarsimp; metis fee1_sum) ;;
           (*TODO: syntax*)
           tick_cross affirm using t2 the_\<phi>(28) by blast ;;
                      affirm using y1 by fastforce ;;
            \<rightarrow> var liquidityNet ;;
            \<open>_ \<Ztypecolon> Ticks\<close> is \<open>(_,_,_,real_next_tick,_)\<close> affirm
                unfolding real_next_tick_def apply (auto simp add: the_\<phi>lemmata(2))
                using x1' apply linarith using x1 by fastforce  ;;

            if \<open>$zeroForOne\<close> \<medium_left_bracket> \<open>- $liquidityNet\<close> \<rightarrow> liquidityNet \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;
              
              \<open>$liquidity + $liquidityNet\<close> \<rightarrow> $liquidity is \<open>L real_next_tick\<close>
                affirm unfolding real_next_tick_def by (smt (verit, ccfv_SIG) t11 t7 x1 x1') ;;
            \<medium_right_bracket>. \<medium_left_bracket> 

              \<open>_ \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] _\<close> is \<open>L real_next_tick\<close>
              affirm unfolding real_next_tick_def
                by (auto,
                    smt (verit, ccfv_threshold) \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> t7 the_\<phi>(10) the_\<phi>(12) the_\<phi>(13) the_\<phi>(28) the_\<phi>lemmata(3) x1 y0,
                    smt (verit, best) \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> kk2 kk4 t11 the_\<phi>(12) the_\<phi>(13) the_\<phi>(27) the_\<phi>(28) the_\<phi>lemmata(3)) ;;
                         
              shift_current_tick[where j=\<open>real_next_tick\<close>]
                  affirm using real_next_tick_dom . ;;
                  affirm by (smt (verit) real_next_tick_def the_\<phi>(10) the_\<phi>(13) the_\<phi>(28) the_\<phi>(3) the_\<phi>lemmata(3) tick_next_def y0);;
        \<medium_right_bracket>. ;;

        \<open>$tick_next - 1\<close> to Tick affirm using kk2 nle_le the_\<phi>(29) tick_next_dom(1) tick_next_dom(2) by force ;;
        $tick_next, $zeroForOne
        sel is \<open>real_next_tick\<close> affirm unfolding real_next_tick_def .. ;; (*TODO: syntax*)
          \<rightarrow> tick 

        have kk5[simp]: \<open>real_next_tick < MAX_TICK\<close> unfolding real_next_tick_def
          by (smt (verit, ccfv_SIG) kk4 the_\<phi>(27) tick_next_dom(2))
      \<medium_right_bracket> for \<open>_ \<s>\<u>\<b>\<j> real_next_tick < MAX_TICK\<close> ..
      \<medium_left_bracket>
        have zx1: \<open>zeroForOne \<Longrightarrow> tick_of_price next_price \<le> j\<close>
          by (smt (verit) kk6 kk8 price_of_L0 price_of_mono price_of_tick the_\<phi>(21))
        have zx2: \<open>\<not> zeroForOne \<Longrightarrow> j \<le> tick_of_price next_price\<close>
          by (metis add1_zle_eq dual_order.strict_trans2 kk9 linorder_not_le price_of_mono price_of_tick t0 the_\<phi>(21))

        have zz6: \<open>zeroForOne \<Longrightarrow> tick_next \<le> tick_of_price next_price\<close>
          by (smt (verit, ccfv_threshold) kk6 price_of_L0 price_of_smono price_of_tick)
        have zz7: \<open>\<not> zeroForOne \<Longrightarrow> tick_of_price next_price < tick_next\<close>
          by (smt (verit, ccfv_threshold) kk2 kk7 price_of_L0 price_of_smono price_of_tick the_\<phi>(27))


        have zxx: \<open>L j = L (tick_of_price next_price)\<close>
          by (metis t11 t7 zx1 zx2 zz6 zz7) ;;

        if \<open>$price \<noteq> $step_price_start\<close> \<medium_left_bracket>
          getTickAtSqrtRatio ($price) affirm using dual_order.strict_trans kk2 price_of_L0 by blast ;;
            \<rightarrow> tick
        \<medium_right_bracket>. \<medium_left_bracket> ;; \<medium_right_bracket>. ;; is \<open>tick_of_price next_price\<close> ;;

        \<open>\<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] _\<close> is \<open>L (tick_of_price next_price)\<close> affirm using zxx . ;;
        shift_current_tick[where j=\<open>tick_of_price next_price\<close>]
          affirm using the_\<phi>(4) the_\<phi>(5) by fastforce ;;
          affirm using y1 zx1 zx2 zz6 zz7 by force ;;


      \<medium_right_bracket>. ;;

      define real2_next_tick where
        \<open>real2_next_tick = (if next_price = price_of tick_next then real_next_tick else tick_of_price next_price)\<close> ;;

      \<open>\<v>\<a>\<r>[\<v>\<a>\<r>_tick] _\<close> is real2_next_tick affirm unfolding real2_next_tick_def by simp ;;
      \<open>\<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] _\<close> is \<open>L real2_next_tick\<close> affirm unfolding real2_next_tick_def by simp ;;
      \<open>_ \<Ztypecolon> Ticks\<close> is \<open>(Lg, L, growth'', real2_next_tick, \<delta>)\<close> affirm unfolding real2_next_tick_def by simp ;;

      have Iv1: \<open>real2_next_tick < MAX_TICK\<close>
        unfolding real2_next_tick_def by (auto simp add: the_\<phi>lemmata(5))
             (metis dual_order.strict_trans kk2 kk4 kk8 less_MAX_PRICE_less_MAX_TICK order_le_imp_less_or_eq price_of_L0 the_\<phi>(21))

      have Iv2: \<open>MIN_PRICE \<le> next_price \<and> next_price < MAX_PRICE\<close>
        using kk2 kk4 kk8 the_\<phi>(21) by linarith

      have Iv3: \<open>if zeroForOne then price_limit \<le> next_price else next_price \<le> price_limit\<close>
        using kk6 kk7 by presburger
        
      have Iv4: \<open>if zeroForOne then growth.fee1 o growth'' = growth.fee1 o growth
                                else growth.fee0 o growth'' = growth.fee0 o growth\<close>
        unfolding growth''_def using the_\<phi>(21) apply auto
        apply (smt (verit) fee1_plus_homo fun_upd_comp fun_upd_triv growth.fee1_def old.prod.case)
        by (smt (verit) fee0_plus_homo fun_upd_comp fun_upd_triv growth.fee0_def old.prod.case) ;;



    thm real_next_tick_def
    
    thm \<phi>


  ;;    require (
 (*TODO: break parathensis scope in multi statements*)


  thm get_slot0_unlock_\<phi>app

end

end