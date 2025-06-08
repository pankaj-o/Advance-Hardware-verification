--====================================================
-- File Name: sync_fifo.vhd
-- Description: Synchronuous FIFO
--====================================================

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

--====================================================
-- Entity
--====================================================

entity sync_fifo is
   generic(
      B : natural := 8;  -- number of data bits, default B=8
      W : natural := 4  -- depth = 2**W, default W=4
   );
   port(
      clk : in std_logic;
      rst : in std_logic;
      read : in std_logic;
      write : in std_logic;
      din : in std_logic_vector(B-1 downto 0);
      empty : out std_logic;
      full : out std_logic;
      dout : out std_logic_vector(B-1 downto 0)
   );
end entity sync_fifo;

--====================================================
-- Architecture
--====================================================

architecture rtl of sync_fifo is
   
   type reg_file_type is array (2**W-1 downto 0) of std_logic_vector(B-1 downto 0);
   
   signal array_reg : reg_file_type;
   signal w_ptr_reg, w_ptr_next, w_ptr_succ : std_logic_vector(W-1 downto 0);
   signal r_ptr_reg, r_ptr_next, r_ptr_succ : std_logic_vector(W-1 downto 0);
   signal full_reg, empty_reg, full_next, empty_next : std_logic;
   signal write_op : std_logic_vector(1 downto 0);
   signal write_en : std_logic;
   
begin
  
   -- register file
   process(clk,rst)
   begin
     if (rst='1') then
        array_reg <= (others=>(others=>'0'));
     elsif (clk'event and clk='1') then
        if write_en='1' then
           array_reg(to_integer(unsigned(w_ptr_reg))) <= din;
        end if;
     end if;
   end process;
   
   -- read port
   dout <= array_reg(to_integer(unsigned(r_ptr_reg)));
   -- write enabled only when FIFO is not full
   write_en <= write and (not full_reg);

   -- fifo control logic: register for read and write pointers
   process(clk,rst)
   begin
      if (rst='1') then
         w_ptr_reg <= (others=>'0');
         r_ptr_reg <= (others=>'0');
         full_reg <= '0';
         empty_reg <= '1';
      elsif (clk'event and clk='1') then
         w_ptr_reg <= w_ptr_next;
         r_ptr_reg <= r_ptr_next;
         full_reg <= full_next;
         empty_reg <= empty_next;
      end if;
   end process;

   -- successive pointer values
   w_ptr_succ <= std_logic_vector(unsigned(w_ptr_reg) + 1);
   r_ptr_succ <= std_logic_vector(unsigned(r_ptr_reg) + 1);

   -- next-state logic for read and write pointers
   write_op <= write & read;
   process(w_ptr_reg,w_ptr_succ,r_ptr_reg,r_ptr_succ,write_op,empty_reg,full_reg)
   begin
      w_ptr_next <= w_ptr_reg;
      r_ptr_next <= r_ptr_reg;
      full_next <= full_reg;
      empty_next <= empty_reg;
      case write_op is
         when "00" => null; -- no op
         when "01" => -- read
            if (empty_reg /= '1') then -- not empty
               r_ptr_next <= r_ptr_succ;
               full_next <= '0';
               if (r_ptr_succ=w_ptr_reg) then
                  empty_next <='1';
               end if;
            end if;
         when "10" => -- write
            if (full_reg /= '1') then -- not full
               w_ptr_next <= w_ptr_succ;
               empty_next <= '0';
               if (w_ptr_succ=r_ptr_reg) then
                  full_next <='1';
               end if;
            end if;
         when others => -- write and read
            w_ptr_next <= w_ptr_succ;
            r_ptr_next <= r_ptr_succ;
      end case;
   end process;
   
   -- flags
   full <= full_reg;
   empty <= empty_reg;
   
end architecture rtl;

--====================================================