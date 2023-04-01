theory UniSWP_TickBitmap
  imports UniSWP_Common
begin

(*will be a good case to test our \<phi>-type-fiction conversion.
Get fiction relation from \<phi>-type relation.*)

type_synonym tick_map = \<open>tick \<Rightarrow> bool\<close>

locale Tickmap_spec =
  fixes Tickmap :: \<open>(fiction, tick_map) \<phi>\<close>
    and op_get_tickmap :: \<open>(VAL, VAL) proc'\<close>
  assumes op_get_tickmap:
    \<open> \<p>\<r>\<o>\<c> op_get_tickmap ri \<lbrace> m \<Ztypecolon> Tickmap\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                          \<longmapsto> m \<Ztypecolon> Tickmap\<heavy_comma> m i \<Ztypecolon> \<v>\<a>\<l> \<bool>\<rbrace> \<close>



end