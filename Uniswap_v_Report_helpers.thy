theory Uniswap_v_Report_helpers
  imports Uniswap_Pool
begin

instantiation list :: (type) plus begin
definition plus_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where [simp]: \<open>plus_list = (@)\<close>
instance ..
end

end