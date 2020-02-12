import Prelude hiding (foldr, map, (++), reverse)

-- Exercise 20-1 FOP SS18

-- List functions
----------------------------------------------------------

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f init [] = init
foldr f init (x:xs) = f x (foldr f init xs)

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

-- Inits
----------------------------------------------------------

-- fmi -> f_map_inits
fmi :: a -> [a] -> [a]
fmi x xs = x : xs

-- ffi -> f_fold_inits
ffi :: a -> [[a]] -> [[a]]
ffi x is = [] : (map (fmi x) is)

inits :: [a] -> [[a]]
inits xs = foldr ffi [[]] xs

-- Tails
----------------------------------------------------------

fft :: a -> [[a]] -> [[a]]
fft x (t:ts) = (x : t) : (t:ts)

tails :: [a] -> [[a]]
tails xs = foldr fft [[]] xs
