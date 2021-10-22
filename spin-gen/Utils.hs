{-
 - filz - a model checked I2C specification                                                                        
 - copyright (c) 2021, ETH Zurich, Systems Group        
 -
 - this program is free software: you can redistribute it and/or modify                                            
 - it under the terms of the gnu general public license as published by                                            
 - the free software foundation, either version 3 of the license, or                                               
 - (at your option) any later version.       
 -
 - this program is distributed in the hope that it will be useful,                                                 
 - but without any warranty; without even the implied warranty of                                                  
 - merchantability or fitness for a particular purpose.  see the                                                   
 - gnu general public license for more details.        
 -
 - you should have received a copy of the gnu general public license                                               
 - along with this program.  if not, see <https://www.gnu.org/licenses/>.                                          
 -}
{-
 - Some utils that are helpful in multiple stages. Utils specific for  
 - a stage/datatype should be defined in the corresponding file.
 -}
module Utils where

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:xs) = Just x

safeLast [] = Nothing
safeLast xs = Just $ last xs

safeAt :: [a] -> Int -> Maybe a
safeAt xs i 
        | (i> -1) && (length xs > i) = Just (xs!!i)
        | otherwise = Nothing
