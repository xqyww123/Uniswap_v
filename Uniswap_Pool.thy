theory Uniswap_Pool
  imports Uniswap_SwapMath Uniswap_Tick_Math Uniswap_TickBitmap Uniswap_Tick
begin

no_notation Reals ("\<real>") (*TODO: use that patch!*)

type_synonym fee_protocol = \<open>nat \<times> nat\<close>

datatype pool = pool (price: real) (tick: int) (unlocked: bool) (liquidity: real)
                     (growth: growth) (fee_protocol: fee_protocol) (protocol_fees: \<open>fee \<times> fee\<close>)

hide_const (open) price tick unlocked liquidity growth fee_protocol protocol_fees

setup \<open>Sign.mandatory_path "pool"\<close>

definition \<open>map_price f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool (f p) t u l gr fp pf)\<close>
lemma map_price[simp]:
  \<open>pool.map_price f (pool p t u l gr fp pf) = pool (f p) t u l gr fp pf\<close>
  unfolding pool.map_price_def by simp

definition \<open>map_tick f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p (f t) u l gr fp pf)\<close>
lemma map_tick[simp]:
  \<open>pool.map_tick f (pool p t u l gr fp pf) = pool p (f t) u l gr fp pf\<close>
  unfolding pool.map_tick_def by simp

definition \<open>map_unlock f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t (f u) l gr fp pf)\<close>
lemma map_unlock[simp]:
  \<open>pool.map_unlock f (pool p t u l gr fp pf) = pool p t (f u) l gr fp pf\<close>
  unfolding pool.map_unlock_def by simp

definition \<open>map_liquidity f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u (f l) gr fp pf)\<close>
lemma map_liquidity[simp]:
  \<open>pool.map_liquidity f (pool p t u l gr fp pf) = pool p t u (f l) gr fp pf\<close>
  unfolding pool.map_liquidity_def by simp

definition \<open>map_growth f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u l (f gr) fp pf)\<close>
lemma map_growth[simp]:
  \<open>pool.map_growth f (pool p t u l gr fp pf) = pool p t u l (f gr) fp pf\<close>
  unfolding pool.map_growth_def by simp

definition \<open>map_fee_protocol f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u l gr (f fp) pf)\<close>
lemma map_fee_protocol[simp]:
  \<open>pool.map_fee_protocol f (pool p t u l gr fp pf) = pool p t u l gr (f fp) pf\<close>
  unfolding pool.map_fee_protocol_def by simp

definition \<open>map_protocal_fees f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u l gr fp (f pf))\<close>
lemma map_protocal_fees[simp]:
  \<open>pool.map_protocal_fees f (pool p t u l gr fp pf) = pool p t u l gr fp (f pf)\<close>
  unfolding pool.map_protocal_fees_def by simp

setup \<open>Sign.parent_path\<close>

  

lemma [\<phi>reason 1000]: \<open> Is_Literal fee\<close> unfolding Is_Literal_def ..

proc (nodef) fee[\<phi>synthesis 1100]:
  input \<open>Void\<close>
  output \<open>fee_rate \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  \<medium_left_bracket> op_const_areal[where x=fee_rate] \<medium_right_bracket>. .


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
    and op_get_fee_protocol_0 :: \<open>VAL proc\<close>
    and op_get_fee_protocol_1 :: \<open>VAL proc\<close>
    and op_get_protocal_fee_0 :: \<open>VAL proc\<close>
    and op_set_protocal_fee_0 :: \<open>(VAL,unit) proc'\<close>
    and op_get_protocal_fee_1 :: \<open>VAL proc\<close>
    and op_set_protocal_fee_1 :: \<open>(VAL,unit) proc'\<close>
  assumes [\<phi>inhabitance_rule]:
    \<open>s \<Ztypecolon> Pool \<i>\<m>\<p>\<l>\<i>\<e>\<s> UNIV \<a>\<n>\<d> 0 < pool.price s \<and> pool.tick s \<in> {MIN_TICK..<MAX_TICK}
                           \<and> pool.price s \<in> {MIN_PRICE..<MAX_PRICE}\<close>
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
    \<open> \<p>\<r>\<o>\<c> op_get_fee_growth_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> growth.fee0 (pool.growth s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_fee_growth_0_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_fee_growth_0 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_growth (growth.map_fee0 (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_fee_growth_1_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_growth_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> growth.fee1 (pool.growth s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_fee_growth_1_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_fee_growth_1 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_growth (growth.map_fee1 (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_fee_protocol_0[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_protocol_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> fst (pool.fee_protocol s) \<Ztypecolon> \<v>\<a>\<l> \<nat> \<rbrace> \<close>
  and get_fee_protocol_1[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_protocol_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> snd (pool.fee_protocol s) \<Ztypecolon> \<v>\<a>\<l> \<nat> \<rbrace> \<close>
  and get_pool_protocal_fee_0_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_protocal_fee_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> fst (pool.protocol_fees s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_protocal_fee_0_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_protocal_fee_0 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_protocal_fees (apfst (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_protocal_fee_1_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_protocal_fee_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> snd (pool.protocol_fees s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_protocal_fee_1_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_protocal_fee_1 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_protocal_fees (apsnd (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>

begin


definition Uniswap_Pool :: \<open>(fiction, price \<times> tick \<times> bool \<times> liquiditys \<times> liquiditys \<times> growths \<times> opt_growths \<times> fee_protocol \<times> (fee \<times> fee)) \<phi>\<close>
  where [\<phi>defs]: \<open>Uniswap_Pool x = (
    case x of (price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Rightarrow>
        \<comment> \<open>\<open>growth\<close> is the abstract growth happened on every tick\<close>
      pool price i unlocked (L i) (gSum growth) fee_proto protocol_fees \<Ztypecolon> Pool\<heavy_comma>
        \<comment> \<open>so the global fee growth is the sum of the \<open>growth\<close> over every tick\<close>
      (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
        \<comment> \<open>\<open>k \<in> dom \<delta>\<close> means the tick \<open>k\<close> is initialized\<close>
      (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks
    \<s>\<u>\<b>\<j> (tick_of_price price = i \<or> price = price_of (i + 1))
)\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 1200]:
  \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Ztypecolon> Uniswap_Pool \<i>\<m>\<p>\<l>\<i>\<e>\<s>
   pool price i unlocked (L i) (gSum growth) fee_proto protocol_fees \<Ztypecolon> Pool\<heavy_comma>
   (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
   (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks
  \<a>\<n>\<d> (tick_of_price price = i \<or> price = price_of (i + 1))
  @action to RAW\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (tick_of_price price = i \<or> price = price_of (i + 1))
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> pool price i unlocked (L i) (gSum growth) fee_proto protocol_fees \<Ztypecolon> Pool\<heavy_comma>
        (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
        (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Ztypecolon> Uniswap_Pool \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<a>\<n>\<d> P\<close>
  unfolding FOCUS_TAG_def
  \<medium_left_bracket> premises _ and I
    I 
    construct\<phi> \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Ztypecolon> Uniswap_Pool\<close>
  \<medium_right_bracket>. .

declare Invt_Ticks_def[simp] Invt_A_Tick_def[simp]

(*
definition swap_loop_transition :: \<open>bool \<Rightarrow> bool \<Rightarrow> nat \<times> nat \<Rightarrow> liquidity \<Rightarrow> tick \<times> fee \<Rightarrow> unit\<close>
  where \<open>swap_loop_transition exactIn zeroForOne fee_protocol L
    =(\<lambda>(j,ar).
      let fee_proto = (if zeroForOne then fst fee_protocol else snd fee_protocol) ;
          (next_price, amountIn, amountOut, fee_amount) =
  swap_step pr (if zeroForOne then max (price_of tick_next) price_limit else min (price_of tick_next) price_limit) (L j) ar fee
       in ())\<close> *)

definition \<open>\<Delta>protocal_fees fee_proto zeroForOne L price price' \<gamma>
    = (if zeroForOne
       then if 0 < fst fee_proto
            then (fst (reserve_change zeroForOne L price price') * fee_rate' / real (fst fee_proto), 0)
            else (0,0)
       else if 0 < snd fee_proto
            then (0, snd (reserve_change zeroForOne L price price') * fee_rate' / real (snd fee_proto))
            else (0,0))\<close>

proc swap:
  input \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_protocol, protocol_fees) \<Ztypecolon> Uniswap_Pool\<heavy_comma>
         zeroForOne \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> amount_specified \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> price_limit \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 \<noteq> amount_specified \<and> 0 < price_limit\<close> and \<open>unlocked\<close>
      and \<open>if zeroForOne then price_limit < price \<and> price_limit > MIN_PRICE
                         else price_limit > price \<and> price_limit < MAX_PRICE\<close>
    (*soon we will not need to declare these pre-conditions but verify that
        a revert will happen once they are violated*)
  output \<open>(price', i', unlocked, Lg, L,
            growth + fee_growth zeroForOne fee_rate' L price price',
            \<delta>, fee_protocol,
            protocol_fees + \<Delta>protocal_fees fee_protocol zeroForOne L price price' fee_rate') \<Ztypecolon> Uniswap_Pool\<heavy_comma>
          transfer_out \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> transfer_in \<Ztypecolon> \<v>\<a>\<l> \<real>
    \<s>\<u>\<b>\<j> price' i' transfer_out transfer_in.
      (if zeroForOne then price_limit \<le> price' else price' \<le> price_limit) \<and>
      (price' = price_limit \<or> (
      if 0 < amount_specified
      then amount_specified * (1 - fee_rate) = (if zeroForOne then fst else snd) (reserve_change zeroForOne L price price')
      else - amount_specified = (if zeroForOne then snd else fst) (reserve_change zeroForOne L price price') ))
      \<comment> \<open>The resulted price either reaches the price limit, or, is the one having a reserve change
             meeting the specified amount.
          \<open>reserve_change zeroForOne L price price'\<close> is the reserve change of token0 and token1
             when the price is moving from \<open>price\<close> to \<open>price'\<close>\<close>
      \<comment> \<open>The tick \<open>i'\<close> is the one satisfying the global invariant encoded in \<^const>\<open>Uniswap_Pool\<close>,
          which is, \<open>i'\<close> is the tick of the \<open>price'\<close>, \<open>price_of i' \<le> price \<le> price_of (i' + 1)\<close>\<close>
      \<comment> \<open>Gross liquidity \<open>Lg\<close>, actual liquidity \<open>L\<close>, the absolute difference \<open>\<delta>\<close> in recorded fee growth,
          and the proportion \<open>fee_protocol\<close> of the protocol fee, are not changed\<close>
      \<comment> \<open>The fee growth \<open>growth + fee_growth zeroForOne fee_rate' L price price'\<close>
          and the \<open>protocol_fees\<close> are increased accordingly.\<close>
   \<and> transfer_out = (if zeroForOne then snd else fst) (reserve_change zeroForOne L price price')
   \<and> transfer_in = (if zeroForOne then fst else snd) (reserve_change zeroForOne L price price') / (1 - fee_rate)
    \<comment> \<open>As \<phi>-system hasn't formalized transfer and external call, we cannot verify the last transfer operation
      in the swap function, but only verify the amount of transfer-out and that of transfer-in. \<close>
\<close>
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

    define fee_proto where \<open>fee_proto = (if zeroForOne then fst fee_protocol else snd fee_protocol)\<close> ;;

    \<open>pool.liquidity _\<close> \<rightarrow> val liquidityStart
    sel (\<open>fst (pool.fee_protocol _)\<close> \<open>snd (pool.fee_protocol _)\<close> $zeroForOne)
        is fee_proto affirm unfolding fee_proto_def by simp ;; \<rightarrow> val feeProtocol
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> val secondsPerLiquidityCumulative
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> val tickCumulative

    (* no blockTimestamp because we don't cover observation *)

    \<open>$amount_specified > 0\<close> \<rightarrow> val exactInput

    define I_fee_growth_global where
      \<open>\<And>gr. I_fee_growth_global gr = (if zeroForOne then global_fee0_growth gr else global_fee1_growth gr)\<close> ;;

    $amount_specified, \<open>0 \<Ztypecolon> \<real>\<close>,
      \<open>pool.price _\<close>, \<open>pool.tick _\<close>,
      sel (\<open>growth.fee0 (pool.growth _)\<close> \<open>growth.fee1 (pool.growth _)\<close> $zeroForOne)
          is \<open>I_fee_growth_global growth\<close> affirm unfolding I_fee_growth_global_def by simp ;;
      \<open>0 \<Ztypecolon> \<real>\<close>, $liquidityStart
    \<rightarrow> var amount_remaining, amount_calculated, price, tick, fee_growth_global, protocolFee, liquidity ;;

    while \<open>ar \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_amount_remaining] \<real>\<heavy_comma>
           pr \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_price] \<real>\<heavy_comma>
           ac \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_amount_calculated] \<real>\<heavy_comma>
           pf \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_protocolFee] \<real>\<heavy_comma>
            j \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_tick] Tick\<heavy_comma>
           L j \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] \<real>\<heavy_comma>
          I_fee_growth_global (growth + fee_growth zeroForOne fee_rate' L price pr) \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_fee_growth_global] \<real>\<heavy_comma>
          (Lg, L, growth + fee_growth zeroForOne fee_rate' L price pr, j, \<delta>) \<Ztypecolon> Ticks
        \<s>\<u>\<b>\<j> ar pr ac pf j.
            Inv: ( MIN_PRICE \<le> pr \<and> pr < MAX_PRICE
                 \<and> j < MAX_TICK
                 \<and> (tick_of_price pr = j \<or> pr = price_of (j + 1))
                 \<and> (if zeroForOne then price_limit \<le> pr \<and> pr \<le> price else price \<le> pr \<and> pr \<le> price_limit)
                 \<and> (let (\<Delta>reserve0, \<Delta>reserve1) = reserve_change zeroForOne L price pr;
                        amountIn = (if zeroForOne then \<Delta>reserve0 else \<Delta>reserve1) ;
                        amountOut = (if zeroForOne then \<Delta>reserve1 else \<Delta>reserve0)
                     in (if ?exactInput then amount_specified - amountIn / (1 - fee_rate) else amount_specified + amountOut) = ar
                      \<and> (if ?exactInput then - amountOut else amountIn / (1 - fee_rate)) = ac
                      \<and> (if 0 < fee_proto then amountIn * fee_rate' / real fee_proto else 0) = pf
                   )
                 
          )
          \<and> Guard: (ar \<noteq> 0 \<and> pr \<noteq> price_limit)\<close>
    \<medium_left_bracket> \<open>$amount_remaining \<noteq> 0 \<and> $price \<noteq> $price_limit\<close> \<medium_right_bracket>.
    \<medium_left_bracket>
      $price \<rightarrow> val step_price_start ;;
      nextInitializedTickWithinOneWord ($tick, $zeroForOne) \<exists>tick_next' \<rightarrow> var tick_next, val initialized ;;

      define tick_next where \<open>tick_next = max MIN_TICK (min MAX_TICK tick_next')\<close> ;;

      if \<open>$tick_next < MIN_TICK\<close> \<medium_left_bracket> \<open>MIN_TICK\<close> \<rightarrow> tick_next \<medium_right_bracket>. \<medium_left_bracket>
        if \<open>$tick_next > MAX_TICK\<close> \<medium_left_bracket> \<open>MAX_TICK\<close> \<rightarrow> tick_next \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;
      \<medium_right_bracket>. as \<open>tick_next \<Ztypecolon> Tick\<close> affirm unfolding tick_next_def using \<phi> by auto ;;

      let ?growth' = \<open>growth + fee_growth zeroForOne fee_rate' L price pr\<close>

      have t0[useful]: \<open>0 < pr\<close> by (smt (verit) the_\<phi>(25) the_\<phi>(3) the_\<phi>(33))

      have t2: \<open>0 < Lg tick_next' \<Longrightarrow> 0 < Lg tick_next\<close> by (smt (verit, ccfv_SIG) \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> the_\<phi>(18))

      have tick_next_dom: \<open>MIN_TICK \<le> tick_next\<close> \<open>tick_next \<le> MAX_TICK\<close> using the_\<phi>(4) the_\<phi>(5) by blast+

      have y0: \<open>if j < tick_next' then next_initialized Lg j tick_next' else next_initialized Lg (tick_next') (j+1)\<close>
        by (auto,
            metis greaterThanLessThan_iff not_less_iff_gr_or_eq order_less_le_trans the_\<phi>(15) the_\<phi>lemmata(4),
            metis dual_order.strict_trans1 greaterThanAtMost_iff order_less_le the_\<phi>(15) the_\<phi>lemmata(4))

      have y1: \<open>if j < tick_next then next_initialized Lg j tick_next else next_initialized Lg tick_next (j+1)\<close>
        using \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> the_\<phi>(6) the_\<phi>(7) y0 by fastforce

      have x1: \<open>zeroForOne \<Longrightarrow> tick_next \<le> j\<close> using the_\<phi>lemmata(2) the_\<phi>lemmata(4) tick_next_def by fastforce

      have x1': \<open>\<not> zeroForOne \<Longrightarrow> j < tick_next\<close> using the_\<phi>(27) the_\<phi>lemmata(4) tick_next_def by force

      have t8: \<open>zeroForOne \<Longrightarrow> \<forall>k. tick_next < k \<and> k \<le> j \<longrightarrow> Lg k = 0\<close> using y1 by force

      have t8': \<open>\<not> zeroForOne \<Longrightarrow> \<forall>k. j < k \<and> k \<le> (tick_next - 1) \<longrightarrow> Lg k = 0\<close> using y1 by force

      have t7: \<open>\<And>k. zeroForOne \<Longrightarrow> tick_next \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> L k = L j\<close>
        subgoal premises Ps for k
          using t8 Ps(2) apply (induct rule: int_le_induct[where k=j and i=k, OF Ps(3)]; simp)
          by (metis Ps(1) the_\<phi>(14)) .

      have t11: \<open>\<And>k. \<not> zeroForOne \<Longrightarrow> k < tick_next \<Longrightarrow> j \<le> k \<Longrightarrow> L k = L j\<close>
        subgoal premises Ps for k
          using t8' Ps(2) apply (induct rule: int_ge_induct[where k=j and i=\<open>k\<close>, OF Ps(3)]; simp)
          using Ps(1) the_\<phi>(14) by fastforce . 

      have lx1: \<open>\<not> zeroForOne \<Longrightarrow> global_fee0_growth ?growth' = global_fee0_growth growth\<close> by (simp add: fee_growth_is_0_when_not_zeroForOne the_\<phi>(25) the_\<phi>(3))

      have lx2: \<open>zeroForOne \<Longrightarrow> global_fee1_growth ?growth' = global_fee1_growth growth\<close> by (simp add: fee_growth_is_0_when_zeroForOne t0 the_\<phi>(25))

      ;;

      getSqrtRatioAtTick ($tick_next) \<rightarrow> val step_price_next ;;

      computeSwapStep (
        $price,
        sel ($price_limit, $step_price_next,
                sel (\<open>$step_price_next < $price_limit\<close>, \<open>$step_price_next > $price_limit\<close>, $zeroForOne))
         is \<open>if zeroForOne then max ?step_price_next price_limit else min ?step_price_next price_limit\<close>,
        $liquidity,
        $amount_remaining,
        fee)
        \<exists>next_price, amountIn, amountOut, fee_amount
     \<rightarrow> val amountIn, amountOut, feeAmount \<rightarrow> price ;;
     (*FIX ME: ^ there is a bug in programming system*)

      have d2: \<open>fee_amount = amountIn * fee_rate'\<close> unfolding fee_rate'_def using swap_step_fee_amout the_\<phi>(19) by force

      have d1[simp]: \<open>amountIn + fee_amount = amountIn / (1 - fee_rate)\<close> by (smt (verit, ccfv_threshold) ab_semigroup_mult_class.mult_ac(1) add.commute add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel comm_semiring_class.distrib d2 diff_add_eq diff_diff_eq2 diff_zero div_by_1 divide_cancel_right divide_divide_eq_left divide_divide_eq_left' divide_divide_eq_right divide_eq_0_iff divide_real_def eq_divide_imp fee_rate_range linorder_not_le minus_diff_eq mult.commute mult.left_commute mult.right_neutral mult_1 mult_cancel_left2 mult_eq_0_iff mult_zero_left mult_zero_right nle_le nonzero_divide_mult_cancel_left nonzero_mult_div_cancel_left order_refl real_divide_square_eq right_diff_distrib' ring_class.ring_distribs(1) times_divide_eq_left fee_rate'_def)

      have t1[simp]: \<open>L j = 0 \<Longrightarrow> fee_amount = 0\<close> using \<open>_ = swap_step _ _ _ _ _\<close> by (auto simp add: swap_step_def Let_def)

      have kk1: \<open>MIN_PRICE < (if zeroForOne then max ?step_price_next price_limit else min ?step_price_next price_limit)\<close> using price_of_smono the_\<phi>(24) the_\<phi>(27) the_\<phi>(31) the_\<phi>(33) the_\<phi>lemmata(2) x1' by force

      have kk2: \<open>MIN_PRICE < next_price\<close> using fee_rate_range kk1 swap_step_next_price_Le_MIN_PRICE the_\<phi>(16) the_\<phi>(25) the_\<phi>(31) the_\<phi>lemmata(5) by blast

      have kk4: \<open>\<not> zeroForOne \<Longrightarrow> next_price < MAX_PRICE\<close> by (smt (verit, best) fee_rate_range price_of_L0 swap_step_next_price_Gt t0 the_\<phi>(16) the_\<phi>(25) the_\<phi>(27) the_\<phi>(33) the_\<phi>lemmata(5))
        
      have kk8: \<open>zeroForOne \<Longrightarrow> next_price \<le> pr\<close> by (smt (verit, best) fee_rate_range price_of_L0 price_of_smono price_of_tick swap_step_next_price_LE_price t0 the_\<phi>(16) the_\<phi>(27) the_\<phi>(28) the_\<phi>lemmata(5) x1) 

      have kk6: \<open>zeroForOne \<Longrightarrow> price_of tick_next \<le> next_price \<and> price_limit \<le> next_price\<close> by (smt (verit, best) fee_rate_range kk8 price_of_L0 swap_step_next_price_Le swap_step_next_price_Le_0 t0 the_\<phi>(16) the_\<phi>(25) the_\<phi>lemmata(5))
        
      have kk9: \<open>\<not> zeroForOne \<Longrightarrow> pr \<le> next_price\<close> by (smt (verit, ccfv_SIG) fee_rate_range price_of_mono price_of_tick swap_step_next_price_Le swap_step_price_target_LE_next_price t0 the_\<phi>(16) the_\<phi>(25) the_\<phi>(27) the_\<phi>(28) the_\<phi>lemmata(5) x1') 

      have kk7: \<open>\<not> zeroForOne \<Longrightarrow> next_price \<le> price_of tick_next \<and> next_price \<le> price_limit\<close>
        apply (auto)
        apply (smt (verit, ccfv_threshold) fee_rate_range kk9 price_of_L0 swap_step_next_price_Gt t0 the_\<phi>(16) the_\<phi>(25) the_\<phi>(27) the_\<phi>lemmata(5))
        by (smt (verit, ccfv_SIG) fee_rate_range price_of_L0 swap_step_next_price_LE_price swap_step_next_price_LE_price_target t0 the_\<phi>(16) the_\<phi>(27) the_\<phi>lemmata(5))

      have ka1: \<open>zeroForOne \<Longrightarrow> \<forall>k. tick_of_price next_price < k \<and> k < tick_of_price pr \<longrightarrow> Lg k = 0\<close> by (metis dual_order.strict_trans2 kk6 order.strict_iff_not price_of_L0 t8 the_\<phi>(28) tick_of_price tick_of_price_LE_mono zle_add1_eq_le)

      have ka2: \<open>\<not> zeroForOne \<Longrightarrow> \<forall>k. tick_of_price pr < k \<and> k < tick_of_price next_price \<longrightarrow> Lg k = 0\<close> by (smt (verit, del_insts) kk2 kk7 price_of_L0 the_\<phi>(28) tick_of_price tick_of_price_LE_mono y1)

      have kb1: \<open>zeroForOne \<Longrightarrow> \<forall>k. next_price \<le> k \<and> k < pr \<longrightarrow> L (tick_of_price k) = L j\<close>
        by (smt (verit) kk6 price_of_L0 price_of_tick t7 the_\<phi>(28) tick_of_price tick_of_price_LE_mono)

      have kb2: \<open>\<not> zeroForOne \<Longrightarrow> \<forall>k. pr \<le> k \<and> k < next_price \<longrightarrow> L (tick_of_price k) = L j\<close>
        by (smt (verit) kk7 price_of_smono price_of_tick t0 t11 the_\<phi>(28))

      have p1: \<open>zeroForOne \<Longrightarrow> L (tick_of_price next_price) = L j\<close>
        by (smt (verit, ccfv_SIG) fee_rate_range kk6 price_of_smono price_of_tick swap_step_next_price_Gt t7 the_\<phi>(16) the_\<phi>(19) the_\<phi>(24) the_\<phi>(25) the_\<phi>(27) the_\<phi>(28) the_\<phi>(35) x1)

      have p2: \<open>if zeroForOne then (amountIn, amountOut) = reserve_change_in_a_step (L (tick_of_price next_price)) next_price pr
                              else (amountOut, amountIn) = reserve_change_in_a_step (L (tick_of_price pr)) pr next_price\<close>
        apply (cases zeroForOne; simp)
        apply (smt (verit, ccfv_SIG) kk6 kk8 p1 swap_step_reserve_change_zeroForOne the_\<phi>lemmata(5))
        by (smt (verit, ccfv_SIG) growth.fee0 growth.fee0.homo_zero growth.fee1 growth.fee1.homo_zero kk7 kk9 price_of_smono reserve_change_in_a_tick_0 swap_step_reserve_change_not_zeroForOne swap_step_reserve_change_zeroForOne t11 the_\<phi>(28) the_\<phi>lemmata(5) tick_of_price)

      have pp1: \<open>zeroForOne \<Longrightarrow> amountIn = (1/next_price - 1/pr) * L j\<close>
        by (metis comm_monoid_mult_class.mult_1 divide_real_def growth.fee0 mult.commute p1 p2 reserve_change_in_a_step_def right_diff_distrib')
      have pp2: \<open>\<not> zeroForOne \<Longrightarrow> amountIn = (next_price - pr) * L j\<close>
        by (smt (verit, ccfv_SIG) growth.fee1 kk7 kk9 mult.commute mult_cancel_right p2 reserve_change_in_a_step_def swap_step_reserve_change_not_zeroForOne the_\<phi>lemmata(5))

      ;;


      if \<open>$exactInput\<close> \<medium_left_bracket>
          \<open>$amount_remaining - ($amountIn + $feeAmount)\<close> \<rightarrow> amount_remaining
          \<open>$amount_calculated - $amountOut\<close> \<rightarrow> amount_calculated
      \<medium_right_bracket>. \<medium_left_bracket>
          \<open>$amount_remaining + $amountOut\<close> \<rightarrow> amount_remaining
          \<open>$amount_calculated + ($amountIn + $feeAmount)\<close> \<rightarrow> amount_calculated
      \<medium_right_bracket>. ;;

      if \<open>$feeProtocol > 0\<close> \<medium_left_bracket>
        \<open>$feeAmount / real $feeProtocol\<close> \<rightarrow> val delta
        \<open>$feeAmount - $delta\<close> \<rightarrow> feeAmount
        \<open>$protocolFee + $delta\<close> \<rightarrow> protocolFee
      \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;

      define step_growth where \<open>step_growth = (if L j = 0 then 0 else fee_amount / L j)\<close>
      define \<Delta>growth where \<open>\<Delta>growth = fee_growth zeroForOne fee_rate' L pr next_price\<close> 

      have ak1: \<open>0 < L j \<Longrightarrow> zeroForOne \<Longrightarrow> global_fee0_growth (fee_growth' True fee_rate' L next_price pr) = (1/next_price - 1/pr) * fee_rate'\<close>
        using gSum_fee_growth kb1 kk2 kk8 the_\<phi>(30) by force

      have ak2: \<open>0 < L j \<Longrightarrow> \<not> zeroForOne \<Longrightarrow> global_fee1_growth (fee_growth' False fee_rate' L pr next_price) = (next_price - pr) * fee_rate'\<close>
        using gSum_fee_growth growth.fee1 kb2 kk4 kk9 the_\<phi>(31) by presburger
        
      ;;

      if \<open>$liquidity > 0\<close> \<medium_left_bracket>
        \<open>$fee_growth_global + ($feeAmount / $liquidity)\<close> \<rightarrow> fee_growth_global
        (*TODO: \<open>fee_growth_0\<close> give interesting result?*)
      \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
      is \<open>I_fee_growth_global (?growth' + \<Delta>growth)\<close>
      affirm unfolding I_fee_growth_global_def \<Delta>growth_def
      apply (auto simp add: zero_fun_def step_growth_def the_\<phi>lemmata(3))
         apply (simp add: ak1 d2 pp1)
      apply (simp add: ak2 d2 pp2)
      apply (smt (verit) gSum_fee_growth_eq_0 growth.fee0.homo_zero kb1 kk2 kk8 the_\<phi>(16) the_\<phi>(30))
      by (smt (verit) gSum_fee_growth_eq_0 growth.fee1 kb2 kk4 kk9 the_\<phi>(16) the_\<phi>(31) zero_prod_def) ;;

      define real_next_tick where \<open>real_next_tick = (if zeroForOne then tick_next - 1 else tick_next)\<close> 

      have real_next_tick_dom[simp]: \<open>real_next_tick \<in> {MIN_TICK - 1..MAX_TICK}\<close>
        using real_next_tick_def tick_next_dom(1) tick_next_dom(2) by force ;;

      if \<open>$price = $step_price_next\<close> \<medium_left_bracket>

        if \<open>$initialized\<close> \<medium_left_bracket>

           $tick_next,

           sel ($fee_growth_global, \<open>growth.fee0 (pool.growth _)\<close>, $zeroForOne)
              is \<open>global_fee0_growth (?growth' + \<Delta>growth)\<close>
              affirm unfolding I_fee_growth_global_def \<Delta>growth_def
                by (auto simp add: zero_fun_def, insert fee_growth_is_0_when_not_zeroForOne kk9 the_\<phi>(1) the_\<phi>(29), force) ;;

           sel (\<open>growth.fee1 (pool.growth _)\<close>, $fee_growth_global, $zeroForOne)
              is \<open>global_fee1_growth (?growth' + \<Delta>growth)\<close>
              affirm unfolding I_fee_growth_global_def \<Delta>growth_def
                by (auto simp add: zero_fun_def) (smt (verit, ccfv_SIG) fee_growth_is_0_when_zeroForOne kk2 kk8 price_of_L0 the_\<phi>(29)) ;;
           (*TODO: syntax*)
           tick_cross[where \<Delta>=\<Delta>growth]
              affirm using t2 the_\<phi>(19) by presburger ;;
              affirm using y1 by fastforce ;;
              affirm unfolding \<Delta>growth_def apply auto
                      using fee_growth_eq_0 kk2 kk8 the_\<phi>(20) the_\<phi>(32) apply force
                      apply (smt (verit, ccfv_threshold) fee_growth_eq_0 kk2 kk8 the_\<phi>(30) the_\<phi>(32) tick_of_price)
                      using x1 apply fastforce
                      using x1 apply fastforce
                      using x1' apply fastforce
                      using x1' apply force
                      using fee_growth_eq_0 kk4 kk9 the_\<phi>(30) the_\<phi>(33) apply auto[1]
                      by (smt (verit, best) fee_growth_eq_0 kk4 kk9 the_\<phi>(20) the_\<phi>(33) tick_of_price) ;;
              affirm unfolding \<Delta>growth_def apply auto
                    using fee_rate'_GT_0 fee_growth_always_ge_0 kk8 the_\<phi>(20) apply force
                    using fee_rate'_GT_0 fee_growth_always_ge_0 kk9 t0 by force ;;
              affirm by (auto simp add: prod_eq_iff growth.fee1_def growth.fee0_def) ;; 
            \<rightarrow> var liquidityNet
            \<open>_ \<Ztypecolon> Ticks\<close> is \<open>(_,_, ?growth' + \<Delta>growth, real_next_tick,_)\<close> affirm
                unfolding real_next_tick_def 
                apply (auto simp add: the_\<phi>lemmata(2) prod_eq_iff)
                using x1' apply linarith
                using x1 by blast ;;

            if \<open>$zeroForOne\<close> \<medium_left_bracket> \<open>- $liquidityNet\<close> \<rightarrow> liquidityNet \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;
              
              \<open>$liquidity + $liquidityNet\<close> \<rightarrow> $liquidity is \<open>L real_next_tick\<close> affirm unfolding real_next_tick_def by (smt (verit, ccfv_SIG) t11 t7 x1 x1') ;;
            \<medium_right_bracket>. \<medium_left_bracket> 

              \<open>_ \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] _\<close> is \<open>L real_next_tick\<close> affirm unfolding real_next_tick_def
              by (auto,
                  smt (verit, del_insts) \<open>tick_next \<in> {MIN_TICK..MAX_TICK} \<and> (if tick_next' < MIN_TICK then MIN_TICK else if MAX_TICK < tick_next' then MAX_TICK else tick_next') = tick_next \<and> True\<close> t7 the_\<phi>(14) the_\<phi>(15) the_\<phi>(19) the_\<phi>(31) x1 y0,
                  smt (verit, ccfv_threshold) kk2 kk4 t11 the_\<phi>(14) the_\<phi>(15) the_\<phi>(19) the_\<phi>(20) the_\<phi>lemmata(4) tick_next_def) ;;

              shift_current_tick_\<Delta>[where j=\<open>real_next_tick\<close> and \<Delta>=\<Delta>growth]
                  affirm using real_next_tick_dom . ;;
                  affirm by (smt (verit) kk2 kk4 kk8 real_next_tick_def the_\<phi>(15) the_\<phi>(19) the_\<phi>(20) the_\<phi>(32) tick_next_def y1) ;;
                  affirm unfolding \<Delta>growth_def real_next_tick_def apply auto
                        using fee_growth_eq_0 kk2 kk8 the_\<phi>(20) the_\<phi>(32) apply force
                        apply (smt (verit, ccfv_threshold) fee_growth_eq_0 kk2 kk8 the_\<phi>(30) the_\<phi>(32) tick_of_price)
                        using x1 apply force
                        using x1 apply fastforce
                        using x1' apply fastforce
                        using x1' apply fastforce
                        using fee_growth_eq_0 kk4 kk9 the_\<phi>(30) the_\<phi>(33) apply auto[1]
                        by (smt (verit, ccfv_threshold) fee_growth_eq_0 kk4 kk9 the_\<phi>(20) the_\<phi>(33) tick_of_price) ;;
                  affirm unfolding \<Delta>growth_def apply auto
                        using fee_rate'_GT_0 fee_growth_always_ge_0 kk6 kk8 the_\<phi>(37) apply force
                        using fee_rate'_GT_0 fee_growth_always_ge_0 kk9 t0 by force ;;

        \<medium_right_bracket>. ;;

        \<open>$tick_next - 1\<close> to Tick affirm using kk2 nle_le the_\<phi>(21) tick_next_dom(1) tick_next_dom(2) by force ;;
        $tick_next, $zeroForOne
        sel is \<open>real_next_tick\<close> affirm unfolding real_next_tick_def .. ;; (*TODO: syntax*)
          \<rightarrow> tick 

        have kk5[simp]: \<open>real_next_tick < MAX_TICK\<close> unfolding real_next_tick_def by (smt (verit, best) kk4 the_\<phi>(19) tick_next_dom(2))

      \<medium_right_bracket> for \<open>_ \<s>\<u>\<b>\<j> real_next_tick < MAX_TICK\<close> ..
      \<medium_left_bracket>
        have zx1: \<open>  zeroForOne \<Longrightarrow> tick_of_price next_price \<le> j\<close> by (smt (verit, best) fee_rate_range kk6 kk8 price_of_L0 price_of_tick swap_step_next_price_Gt the_\<phi>(16) the_\<phi>(20) the_\<phi>(25) the_\<phi>(26) the_\<phi>(29) tick_of_price tick_of_price_LE_mono x1) 
        have zx2: \<open>\<not> zeroForOne \<Longrightarrow> j \<le> tick_of_price next_price\<close> by (smt (verit, best) kk9 t0 the_\<phi>(29) tick_of_price tick_of_price_LE_mono)

        have zz6: \<open>  zeroForOne \<Longrightarrow> tick_next \<le> tick_of_price next_price\<close> by (metis (full_types) kk6 price_of_L0 tick_of_price tick_of_price_LE_mono)
        have zz7: \<open>\<not> zeroForOne \<Longrightarrow> tick_of_price next_price < tick_next\<close> by (smt (verit) kk7 kk9 price_of_tick t0 the_\<phi>(19) tick_of_price tick_of_price_LE_mono)

        have zxx: \<open>L j = L (tick_of_price next_price)\<close> by (metis t11 t7 zx1 zx2 zz6 zz7) ;;

        if \<open>$price \<noteq> $step_price_start\<close> \<medium_left_bracket>
          getTickAtSqrtRatio ($price) affirm using dual_order.strict_trans kk2 price_of_L0 by blast ;;
            \<rightarrow> tick
      \<medium_right_bracket>. \<medium_left_bracket> ;; \<medium_right_bracket>. ;; is \<open>tick_of_price next_price\<close>
          affirm by (smt (verit, best) fee_rate_range kk7 swap_step_next_price_Le t0 the_\<phi>(18) the_\<phi>(22) the_\<phi>(27) the_\<phi>(28) the_\<phi>(31) tick_of_price zx1 zz7) ;;

        \<open>\<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] _\<close> is \<open>L (tick_of_price next_price)\<close> affirm using zxx . ;; ;;
        shift_current_tick_\<Delta>[where j=\<open>tick_of_price next_price\<close> and \<Delta>=\<Delta>growth]
          affirm using the_\<phi>(4) the_\<phi>(5) by fastforce ;;
          affirm using y1 zx1 zx2 zz6 zz7 by force ;;
          affirm unfolding \<Delta>growth_def real_next_tick_def apply auto
              using fee_growth_eq_0 kk2 kk8 the_\<phi>(33) apply auto[1]
              apply (smt (verit) fee_growth_eq_0 kk2 kk8 the_\<phi>(31) the_\<phi>(33) tick_of_price)
              using zx1 apply blast
              using zx1 apply fastforce
              using fee_growth_eq_0 kk4 kk9 the_\<phi>(31) the_\<phi>(34) apply auto[1]
              using fee_growth_eq_0 kk4 kk9 the_\<phi>(34) apply force
              using fee_growth_eq_0 kk4 kk9 the_\<phi>(31) the_\<phi>(34) apply auto[1]
              using fee_growth_eq_0 kk4 kk9 the_\<phi>(34) by blast ;;
              affirm unfolding \<Delta>growth_def
              using fee_rate'_GT_0 fee_growth_always_ge_0 kk6 kk8 kk9 t0 the_\<phi>(38) by auto 
      \<medium_right_bracket>. ;;

      define real2_next_tick where
        \<open>real2_next_tick = (if next_price = price_of tick_next then real_next_tick else tick_of_price next_price)\<close> ;;

      \<open>\<v>\<a>\<r>[\<v>\<a>\<r>_tick] _\<close> is real2_next_tick affirm unfolding real2_next_tick_def by simp ;;
      \<open>\<v>\<a>\<r>[\<v>\<a>\<r>_liquidity] _\<close> is \<open>L real2_next_tick\<close> affirm unfolding real2_next_tick_def by simp ;;
      \<open>_ \<Ztypecolon> Ticks\<close> is \<open>(Lg, L, ?growth' + \<Delta>growth, real2_next_tick, \<delta>)\<close> affirm unfolding real2_next_tick_def by simp

      have Iv1: \<open>real2_next_tick < MAX_TICK\<close>
        unfolding real2_next_tick_def apply (auto simp add: the_\<phi>lemmata(5))
        using the_\<phi>lemmata(6) apply fastforce
        using kk4 kk6 kk8 kk9 less_MAX_PRICE_less_MAX_TICK t0 the_\<phi>(24) the_\<phi>(29) by fastforce
             

      have Iv2: \<open>MIN_PRICE \<le> next_price \<and> next_price < MAX_PRICE\<close> using kk2 kk4 kk8 the_\<phi>(24) by force
      
      have Iv3: \<open>tick_of_price next_price = real2_next_tick \<or> next_price = price_of (real2_next_tick + 1)\<close>
          unfolding real2_next_tick_def real_next_tick_def by auto

      have Iv4: \<open>if zeroForOne then price_limit \<le> next_price \<and> next_price \<le> price
                               else price \<le> next_price \<and> next_price \<le> price_limit\<close>
        using kk6 kk7 kk8 kk9 the_\<phi>(21) by auto

      have p3: \<open>if zeroForOne then Const_Interval (L o tick_of_price) next_price pr
                              else Const_Interval (L o tick_of_price) pr next_price\<close>
        apply (auto simp add: Const_Interval_def)
        using kk8 apply fastforce
        using kb1 apply force
        using kk9 apply blast
        using kb2 by fastforce

      have Iv6: \<open>if zeroForOne then reserve_change' L next_price price = (amountIn, amountOut) + reserve_change' L pr price
                          else reserve_change' L price next_price = reserve_change' L price pr + (amountOut, amountIn)\<close>
        apply auto
        apply (smt (verit, best) add.commute kk6 p2 p3 price_of_L0 reserve_change_add_left the_\<phi>(21))
        using p2 p3 reserve_change_add_right the_\<phi>(2) the_\<phi>(21) by presburger

      have Iv5: \<open>?growth' + \<Delta>growth = growth + fee_growth zeroForOne fee_rate' L price next_price\<close>
        unfolding \<Delta>growth_def by (auto,
            smt (verit, del_insts) Iv2 ab_semigroup_add_class.add_ac(1) add.commute fee_growth_add_right kk8 price_of_L0 the_\<phi>(21),
            metis fee_growth_add_right group_cancel.add1 kk9 the_\<phi>(2) the_\<phi>(21))
        
      ;;
      \<medium_right_bracket> using \<open>let _ = _ in _\<close> by (auto simp add: Iv1 Iv2 Iv3 Iv4 Iv5 Iv6 d2 add_divide_distrib distrib_right)
    ;; affirm apply (auto simp add: \<phi> zero_prod_def)
    using the_\<phi>(16) apply fastforce
    using the_\<phi>(16) apply fastforce
    using the_\<phi>(16) apply fastforce
    using the_\<phi>(16) by fastforce ;;
    \<exists>amount_remaining', price', amount_calculated', proto_fee', i' ;;

  set_pool_tick ($tick)
  set_pool_price ($price) ;;

  if \<open>$liquidityStart \<noteq> $liquidity\<close> \<medium_left_bracket> set_pool_liquidity ( $liquidity ) \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
      is \<open>pool _ _ _ (L i') _ _ _\<close> affirm by auto ;;

  have \<open>zeroForOne \<Longrightarrow>
    growth.map_fee0 (\<lambda>_. I_fee_growth_global (growth + fee_growth zeroForOne fee_rate' L price price')) (gSum growth)
      = gSum (growth + fee_growth zeroForOne fee_rate' L price price')\<close>
    apply (auto simp add: prod_eq_iff growth.map_fee0_def I_fee_growth_global_def growth.fee0_def)
    by (metis fee_growth_is_0_when_zeroForOne growth.fee1_def the_\<phi>(1) the_\<phi>lemmata(6))

  have proto_fee': \<open>proto_fee' =
    (if 0 < fee_proto then ((if zeroForOne then fst else snd) (reserve_change zeroForOne L price price')) * fee_rate' / real fee_proto else 0)\<close>
    by (smt (verit) fee_rate'_def split_def the_\<phi>(16) times_divide_eq_right)

  have proto_fee'_LE0: \<open>0 \<le> proto_fee'\<close>
    unfolding proto_fee' using \<open>0 < price\<close> fee_rate'_GT_0 reserve_change'_LE_0' the_\<phi>(1) the_\<phi>(12) the_\<phi>lemmata(6) by force ;;

  if \<open>$zeroForOne\<close> \<medium_left_bracket>
    set_pool_fee_growth_0 ($fee_growth_global)
    is \<open>pool _ _ _ _ (gSum (growth + fee_growth zeroForOne fee_rate' L price price')) _ _\<close>
    affirm by (auto simp add: prod_eq_iff growth.map_fee0_def I_fee_growth_global_def growth.fee0_def growth.fee1_def the_\<phi>(15)) (metis fee_growth_is_0_when_zeroForOne growth.fee1_def the_\<phi>(1) the_\<phi>(15) the_\<phi>(18)) ;;

    if \<open>$protocolFee > 0\<close> \<medium_left_bracket> set_pool_protocal_fee_0 (\<open>fst (pool.protocol_fees _) + $protocolFee\<close>) \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;

   \<medium_right_bracket>. \<medium_left_bracket>
    set_pool_fee_growth_1 ($fee_growth_global)
    is \<open>pool _ _ _ _ (gSum (growth + fee_growth zeroForOne fee_rate' L price price')) _ _\<close>
    affirm by (auto simp add: prod_eq_iff growth.map_fee1_def I_fee_growth_global_def growth.fee0_def growth.fee1_def the_\<phi>(15)) (metis \<open>0 < price\<close> fee_growth_is_0_when_not_zeroForOne growth.fee0_def the_\<phi>(15) the_\<phi>(18))  ;;

    if \<open>$protocolFee > 0\<close> \<medium_left_bracket> set_pool_protocal_fee_1 (\<open>snd (pool.protocol_fees _) + $protocolFee\<close>) \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;

  \<medium_right_bracket>.
  is \<open>pool price' i' False (L i') (gSum (growth + fee_growth zeroForOne fee_rate' L price price')) fee_protocol
           (protocol_fees + \<Delta>protocal_fees fee_protocol zeroForOne L price price' fee_rate')\<close>
  affirm apply (cases protocol_fees; auto simp add: \<Delta>protocal_fees_def fee_proto_def proto_fee' zero_prod_def)
    using fee_proto_def proto_fee' proto_fee'_LE0 zero_prod_def apply fastforce
    using fee_proto_def proto_fee' proto_fee'_LE0 zero_prod_def apply fastforce
    using fee_proto_def proto_fee' proto_fee'_LE0 apply force
    using fee_proto_def proto_fee' proto_fee'_LE0 by fastforce ;;


  ;; if \<open>$zeroForOne = $exactInput\<close>
      \<medium_left_bracket> \<open>$amount_specified - $amount_remaining\<close>, $amount_calculated \<medium_right_bracket>.
      \<medium_left_bracket> $amount_calculated, \<open>$amount_specified - $amount_remaining\<close> \<medium_right_bracket>. \<rightarrow> val amount0, amount1 ;;
  
  $amount0 is \<open>if zeroForOne then fst (reserve_change' L price' price) / (1 - fee_rate)
                    else - fst (reserve_change' L price price')\<close>
  affirm by (auto; insert the_\<phi>(16), force) ;; \<rightarrow> val amount0

  $amount1 is \<open>if zeroForOne then - snd (reserve_change' L price' price)
                    else snd (reserve_change' L price price') / (1 - fee_rate)\<close>
  affirm by (auto; insert the_\<phi>(16), force) ;; \<rightarrow> val amount1

  if \<open>$zeroForOne\<close> \<medium_left_bracket>
    if \<open>$amount1 < 0\<close> \<medium_left_bracket> \<open>-$amount1\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>0 \<Ztypecolon> \<real>\<close> \<medium_right_bracket>.
    is \<open>snd (reserve_change' L price' price)\<close>
    affirm apply auto
        apply (smt (verit) reserve_change'_LE_0' the_\<phi>(1) the_\<phi>(12) the_\<phi>lemmata(6))
        using the_\<phi>(15) apply blast
        using the_\<phi>(15) by force ;;

    $amount0 is \<open>fst (reserve_change' L price' price) / (1 - fee_rate)\<close>
  \<medium_right_bracket>. \<medium_left_bracket>
    if \<open>$amount0 < 0\<close> \<medium_left_bracket> \<open>-$amount0\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>0 \<Ztypecolon> \<real>\<close> \<medium_right_bracket>.
    is \<open>fst (reserve_change' L price price')\<close>
    affirm by (auto simp add: the_\<phi>(15)) (smt (verit) \<open>0 < price\<close> reserve_change'_LE_0' the_\<phi>(12) the_\<phi>(15) the_\<phi>lemmata(6)) ;;

    $amount1 is \<open>snd (reserve_change' L price price') / (1 - fee_rate)\<close>
  \<medium_right_bracket>. ;;

  set_pool_unlock (\<open>True\<close>)

  \<medium_right_bracket> apply (auto simp add: \<phi>)
    apply (smt (verit, best) \<open>(if zeroForOne = (0 < amount_specified) then amount_specified - amount_remaining' else amount_calculated') = (if zeroForOne then fst (reserve_change' L price' price) / (1 - fee_rate) else - fst (reserve_change' L price price'))\<close> fee_rate_range nonzero_divide_eq_eq the_\<phi>lemmata(8))
    using \<open>(if zeroForOne = (0 < amount_specified) then amount_calculated' else amount_specified - amount_remaining') = (if zeroForOne then - snd (reserve_change' L price' price) else snd (reserve_change' L price price') / (1 - fee_rate))\<close> the_\<phi>lemmata(8) apply force
    using \<open>(if zeroForOne = (0 < amount_specified) then amount_calculated' else amount_specified - amount_remaining') = (if zeroForOne then - snd (reserve_change' L price' price) else snd (reserve_change' L price price') / (1 - fee_rate))\<close> \<open>0 \<noteq> amount_specified \<and> 0 < price_limit\<close> the_\<phi>lemmata(8) apply force
    using \<open>(if zeroForOne = (0 < amount_specified) then amount_specified - amount_remaining' else amount_calculated') = (if zeroForOne then fst (reserve_change' L price' price) / (1 - fee_rate) else - fst (reserve_change' L price price'))\<close> the_\<phi>lemmata(8) by force .

end

end