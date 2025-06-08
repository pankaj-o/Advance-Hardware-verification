-- VHDL model for a 4-bit gray-encoded counter

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity gray is
  port ( clk : in std_logic;
	 rst_n : in std_logic;
	 en : in std_logic;
	 dout : out unsigned (3 downto 0) );
end entity gray;

architecture rtl of gray is
  signal dout_next : unsigned (3 downto 0);
  signal dout_i    : unsigned (3 downto 0);
  
  begin
  process (clk,rst_n)
  begin
    if rst_n = '0' then
      dout_i <= (others => '0') ;
    elsif rising_edge(clk) then
      if en = '1' then
        dout_i <= dout_next ;
      end if;
    end if;
  end process;
  dout <= dout_i;
  process (dout_i)
  begin  
    case dout_i is
      when "0000" => dout_next <= "0001";
      when "0001" => dout_next <= "0011";
      when "0011" => dout_next <= "0010";
      when "0010" => dout_next <= "0110";
      when "0110" => dout_next <= "0111";
      when "0111" => dout_next <= "0101";
      when "0101" => dout_next <= "0100";
      when "0100" => dout_next <= "1100";
      when "1100" => dout_next <= "1101";
      when "1101" => dout_next <= "1111";
      when "1111" => dout_next <= "1110";
      when "1110" => dout_next <= "1010";
      when "1010" => dout_next <= "1011";
      when "1011" => dout_next <= "1001";
      when "1001" => dout_next <= "1000";
      when "1000" => dout_next <= "0000";
      when others => dout_next <= "0000";
    end case;
  end process;

end architecture rtl;

-- EOF