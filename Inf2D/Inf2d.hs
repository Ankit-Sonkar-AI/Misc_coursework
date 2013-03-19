-- Inf2d Assignment 1 2011-12 
-- Matriculation number: 1024819

module Inf2d where

import Data.List
import Data.Maybe
import CSPframework
import Examples

{- NOTES:

-- DO NOT CHANGE THE NAMES OR TYPE DEFINITIONS OF THE FUNCTIONS!
You can write new auxillary functions, but don't change the names or type definitions 
of the functions which you are asked to implement.

-- Comment your code.

-- You should submit this file, and only this file, when you have finished the assignment.

-- The deadline is: 27th of February 2012.

-- See the reference manual for more information on the datatypes and functions of the framework.

-- See www.haskell.org for haskell revision.

-- Useful haskell topics, which you should revise:
-- Recursion
-- Currying
-- The Maybe monad
-- Higher-order functions
-- List processing functions: map, foldl, filter, sortBy etc.

-}

-------------------------------------------------
-- (3) Sudoku problem
-------------------------------------------------

-- (3.i) Variables & values

houses = [1..5]

cluedo_vars :: [Var]
cluedo_vars = ["Miss Scarlett", "Colonel Mustard", "Reverend Green", "Mrs. Peacock", "Professor Plum", "Lead pipe", "Revolver", "Candlestick", "Dagger", "Rope", "Kitchen", "The lounge", "Billiard room", "Library", "Dining room", "Accomplice", "Innocent", "Sleeping", "Studying", "Murderer", "Green", "Red", "Blue", "Yellow", "White"]
--cluedo_vars = ["Billiard room", "Professor Plum", "Yellow", "White", "Green", "Miss Scarlett", "Mrs. Peacock", "Kitchen", "Colonel Mustard", "Innocent", "Reverend Green","Candlestick", "Red", "Blue", "Lead pipe", "Library", "Revolver", "Dagger", "Sleeping", "Rope", "The lounge", "Dining room", "Accomplice", "Studying", "Murderer"]
--cluedo_vars = ["Red", "Green", "Yellow", "Blue", "White", "Miss Scarlett", "Reverend Green", "Mrs. Peacock", "Colonel Mustard", "Professor Plum", "Candlestick", "Dagger", "Lead pipe", "Revolver", "Rope", "Kitchen", "The lounge", "Billiard room", "Library", "Dining room", "Murderer", "Accomplice", "Sleeping", "Studying", "Innocent"]


cluedo_domains :: Domains
cluedo_domains = map (\r -> (r, houses)) cluedo_vars



-- (3.ii) Constraints


-- Unary constraint stating that a variable must have a specific value.
has_value_constraint :: Var -> Int -> Constraint
has_value_constraint v i = CT (v ++ " = " ++ (show i),[v],has_value i)

-- Relation that ensures a variable has a given value.
-- It is satisfied if the variable is unassigned.
has_value :: Int -> Relation
has_value i var assignment
  | ((is_unassigned assignment $ (head var)) == True) = True
  | otherwise = (t == i)
    where t = fromJust(lookup_var assignment $ (head var))

-- Binary constraint stating that two variables must be equal.
vars_same_constraint :: Var -> Var -> Constraint
vars_same_constraint a b = CT (a ++ " = " ++ b,[a,b],vars_same)

-- Relation that ensures two variables are the same.
-- It is satisfied if either variable is unassigned.
vars_same :: Relation
vars_same vars assignment 
 | ((is_unassigned assignment a) == True) || ((is_unassigned assignment b) == True) = True
 | vals_eq (lookup_var assignment a) (lookup_var assignment b) = True
 | otherwise = False
  where a = head vars
        b = head $ tail vars



-- (3.iii) Cluedo CSP

cluedo_csp :: CSP
cluedo_csp = CSP ("Cluedo!",
             cluedo_domains, [ 
		                       (all_diff_constraint ["Red", "Green", "Yellow", "White", "Blue"]),
                               (all_diff_constraint ["Miss Scarlett", "Reverend Green", "Mrs. Peacock", "Colonel Mustard", "Professor Plum"]),
                               (all_diff_constraint ["Candlestick", "Dagger", "Lead pipe", "Revolver", "Rope"]),
                               (all_diff_constraint ["Kitchen", "The lounge", "Billiard room", "Library", "Dining room"]),
                               (all_diff_constraint ["Murderer", "Accomplice", "Sleeping", "Studying", "Innocent"]),
                               (vars_same_constraint "Miss Scarlett" "Green"), -- clue 1
                               (vars_same_constraint "Colonel Mustard" "Innocent"), -- clue 2
                               (vars_same_constraint "Red" "The lounge"), -- clue 3
                               (vars_same_constraint "Mrs. Peacock" "Kitchen"), -- clue 4
                               (diff_one_constraint "Red" "Blue"), -- clue 5
                               (vars_same_constraint "Dagger" "Sleeping"), -- clue6
                               (vars_same_constraint "Lead pipe" "Yellow"), -- clue 7
                               (has_value_constraint "Billiard room" 3), -- clue 8
                               (has_value_constraint "Professor Plum" 1), -- clue 9 
                               (abs_diff_one_constraint "Accomplice" "Rope"), -- clue 10 
                               (abs_diff_one_constraint "Lead pipe" "Studying"), -- clue 11
                               (vars_same_constraint "Revolver" "Library"), -- clue 12
                               (vars_same_constraint "Reverend Green" "Candlestick"), --clue 13
                               (abs_diff_one_constraint "Professor Plum" "White") -- clue 14
               ])
            


-------------------------------------------------
-- (4.1) Forward Checking
-------------------------------------------------


-- (4.1.i) Forward check for constraint propagation:
--We give this function a variable and it checks if it consistent and then removes
--all the incosistent variables

check_var :: Var -> (CSP, Bool, Assignment)-> (CSP, Bool, Assignment)
check_var var (csp, boolean, assignment)= foldr (check_value var) (csp, boolean, assignment) domain 
           where
               domain = domain_of csp var

-- given assignment, csp, variable and value it checks whether the value is 
-- consistent with the given assignment when applied to the variable

check_value :: Var -> Int ->  (CSP, Bool, Assignment) -> (CSP, Bool, Assignment)
check_value var value (csp, boolean, assignment) | is_consistent = (csp, boolean, assignment)
                                                 | otherwise = (del_domain_val csp var value, boolean && not final_var, assignment)
                                                   where
                                                        is_consistent = is_consistent_value csp assignment var value
                                                        final_var =  length(domain_of csp var) == 1  
-- helper function, which was made because I had trouble passing the assignment
-- as a separate function argument and making it work

helper :: CSP -> Assignment -> Var -> (CSP, Bool, Assignment) 
helper csp assignment var = foldr check_var (csp, True, assignment) neighbours_var
          where neighbours_var = all_neighbours_of csp var


forwardcheck :: CSP -> Assignment -> Var -> (CSP, Bool)
forwardcheck csp assignment var = (csp_new, boolean)
                    where (csp_new, boolean, _) = helper csp assignment var

-- (4.1.ii) Algorithm:

fc_recursion :: Assignment -> CSP -> (Maybe Assignment, Int)
fc_recursion assignment csp  = if (is_complete csp assignment) then (Just assignment,0)
    else find_consistent_value $ domain_of csp var
      where var = get_unassigned_var csp assignment
            find_consistent_value vals = 
              case vals of
                []     -> (Nothing,0)
                val:vs -> 
                  if (is_consistent_value csp_new assignment var val) && my_boolean
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fc_recursion (assign assignment var val) csp_new      
                           (ret,nodes') = find_consistent_value vs
                           (csp_new, my_boolean) = forwardcheck csp (assign assignment var val) var

fc :: CSP -> (Maybe Assignment,Int)
fc csp = fc_recursion [] csp 


-------------------------------------------------
-- (4.2) Minimum Remaining Values (MRV)
-------------------------------------------------

-- (4.2.i) Sorting function for variables based on the MRV heuristic:

mrv_compare :: CSP -> Var -> Var -> Ordering
mrv_compare csp var1 var2 
    | length (domain_of csp var1) > length(domain_of csp var2) = GT
    | length (domain_of csp var1) == length(domain_of csp var2) = EQ
    | otherwise = LT


-- (4.2.ii) Get next variable according to MRV for the FC algorithm:

get_mrv_variable :: CSP -> Assignment -> Var
get_mrv_variable csp assignment = head(sortBy (mrv_compare csp) $ [var | var <- (vars_of csp), is_unassigned assignment var])

-- (4.2.iii) FC + MRV algorithm

fc_mrv_recursion :: Assignment -> CSP -> (Maybe Assignment, Int)
fc_mrv_recursion assignment csp  = if (is_complete csp assignment) then (Just assignment,0)
    else find_consistent_value $ domain_of csp var
      where var =  get_mrv_variable csp assignment
            find_consistent_value vals = 
              case vals of
                []     -> (Nothing,0)
                val:vs -> 
                  if (is_consistent_value csp_new assignment var val) && my_boolean
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fc_mrv_recursion (assign assignment var val) csp_new      
                           (ret,nodes') = find_consistent_value vs
                           (csp_new, my_boolean) = forwardcheck csp (assign assignment var val) var


fc_mrv :: CSP -> (Maybe Assignment,Int)
fc_mrv csp = fc_mrv_recursion [] csp 


-------------------------------------------------
-- (4.3) Least Constraining Value (LCV)
-------------------------------------------------

-- (4.3.i) Function that returns the number of choices available for all neighbours
--         of a variable:

num_choices :: CSP -> Assignment -> Var -> Int
num_choices csp assignment var = sum[length([val | val <- domain_of csp x, is_consistent_value csp assignment var val]) | x <- neighbours]
                                    where neighbours = all_neighbours_of csp var

-- (4.3.ii) Function that sorts the domain of a variable based on the LCV heuristic.

lcv_sort :: CSP -> Assignment -> Var -> [Int]
lcv_sort csp assignment var = sortBy (lcv_sort_helper csp assignment var) $ domain_of csp var

-- small helper function that gives ordering for variable and two values

lcv_sort_helper :: CSP -> Assignment -> Var ->  Int -> Int -> Ordering
lcv_sort_helper csp assignment var a b = compare (num_choices csp (assign assignment var a) var) (num_choices csp (assign assignment var b) var)

-- (4.3.iii) FC + LCV algorithm

fc_lcv_recursion :: Assignment -> CSP -> (Maybe Assignment, Int)
fc_lcv_recursion assignment csp  = if (is_complete csp assignment) then (Just assignment,0)
    else find_consistent_value $ lcv_sort csp assignment var
      where var = get_unassigned_var csp assignment
            find_consistent_value vals = 
              case vals of
                []     -> (Nothing,0)
                val:vs -> 
                  if (is_consistent_value csp_new assignment var val) && my_boolean
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fc_lcv_recursion (assign assignment var val) csp_new      
                           (ret,nodes') = find_consistent_value vs
                           (csp_new, my_boolean) = forwardcheck csp (assign assignment var val) var


fc_lcv :: CSP -> (Maybe Assignment,Int)
fc_lcv csp = fc_lcv_recursion [] csp 


-- (4.3.iv) FC + MRV + LCV algorithm

fc_mrv_lcv_recursion :: Assignment -> CSP -> (Maybe Assignment, Int)
fc_mrv_lcv_recursion assignment csp  = if (is_complete csp assignment) then (Just assignment,0)
    else find_consistent_value $ lcv_sort csp assignment var
      where var =  get_mrv_variable csp assignment
            find_consistent_value vals = 
              case vals of
                []     -> (Nothing,0)
                val:vs -> 
                  if (is_consistent_value csp_new assignment var val) && my_boolean
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fc_mrv_lcv_recursion (assign assignment var val) csp_new      
                           (ret,nodes') = find_consistent_value vs
                           (csp_new, my_boolean) = forwardcheck csp (assign assignment var val) var

fc_mrv_lcv :: CSP -> (Maybe Assignment,Int)
fc_mrv_lcv csp = fc_mrv_lcv_recursion [] csp




-------------------------------------------------
-- (5) Evaluation
-------------------------------------------------
{-
  (5.ii) Table:

----------+--------+--------+--------+---------+----------+---------+-----------+
          |   BT   |   FC   | FC+MRV | FC+LCV  |FC+MRV+LCV|   AC3   |AC3+MRV+LCV|
----------+--------+--------+--------+---------+----------+---------+-----------+
aus_csp   |     37 |    11  |    6   |    11   |     6    |         |           |
map_csp   |   1176 |    23  |   15   |    23   |    15    |         |           |
ms3x3_csp |   3654 |   195  |  110   |   195   |   110    |xxxxxxxxx|xxxxxxxxxxx|
cluedo_csp|  20065 |  3124  |   70   |  3124   |    70    |         |           |
----------+--------+--------+--------+---------+----------+---------+-----------+

  (5.iii - 5.iv) Report:

- Your report must be no longer than one A4 page for the first four algorithms
  and another maximum half page for AC3 and AC3+MRV+LCV.
- Write your report starting here. -
-------------------------------------------------
I cannot say that I expected the exact same values, but considering the CSPs we
have I’d say these values are pretty much expected. In the case of the Cluedo 
CSP the variable ordering place a big part in the amount of nodes visited.
In one of the cases, the BT algorithm returned 300 thousand nodes visited
and with a smart ordering of the variables, suggested by Nickolay Bogoytchev 
the amount of nodes decreased to 675.  Since the Cluedo contains 25 variables
and quite a big number of constraints it’s the 2nd worse CSP in terms of notes
visited after the Sudoku. 

-	BT vs. FC:
As expected forward checking always performs better than the backtracking
algorithm.  Backtracking is a depth-first search algorithm that maintains 
consistency of the current and all the past variables. Because of that it 
explores all the possible nodes (partial assignments), backtracks if it indicates 
failure and then goes on until it finds a solution. Forward check in comparison, 
maintains consistency not only of the current and past variable but also of 
the future variables and discards nodes which will not lead to a solution, thus
the smaller branching factor and the much smaller number of notes visited. 

-	FC vs. FC+MRV
The minimum remaining value heuristics always improves the results. The amount 
of improvement however varies with the CSP. In the case with the Cluedo it 
removed around 97% of the nodes visited and reduced the number from 3124 down 
to 70. So it’s a definitely worth improvement. 

-	FC vs. FC+LCV
The least constraining value heuristics did not produce the expected results in
my case. After some discussion with my fellow students and review of the code,
we concluded that theoretically it should produce results a bit better than the
pure FC implementation, however in my case it just returns the same number of 
nodes as the FC. 

-	FC+MRV vs. FC+LCV
In all of the cases, as it can be seen in the chart, the FC+MRV combination 
significantly outperforms the FC+LCV algorithm. Partially due to the fact that
my values for FC and FC+LCV are exactly the same, while the FC+MRV are much
better than the FC ones. 

-	FC+MRV vs. FC+MRV+LCV
In this comparison, I can say that the values are exactly the same. Most likely
due to the fact that LCV did not give any performance improvement at all in my 
case, and minor improvement in some of my fellow students CSPs.

-------------------------------------------------
- End of report-
-}


-------------------------------------------------
-- (6) Arc Consistency
-------------------------------------------------


-- (6.i) Checks if there exists at least one value in a list of values that if 
-- assigned to the given variable the assignment will be consistent.

exists_consistent_value :: CSP -> Var -> Int -> Var -> [Int] -> Bool
exists_consistent_value = undefined


-- (6.ii) AC-3 constraint propagation

revise :: CSP -> Var -> Var -> (CSP,Bool)
revise = undefined


-- (6.iii) AC-3 constraint propagation
        
ac3_check :: CSP -> [(Var,Var)] -> (CSP,Bool)
ac3_check = undefined


-- (6.iv) AC-3 algorithm

ac3_recursion :: Assignment -> CSP -> (Maybe Assignment, Int)
ac3_recursion = undefined


ac3 :: CSP -> (Maybe Assignment,Int)
ac3 csp = ac3_recursion [] csp 



-- (6.v) AC-3 algorithm + MRV heuristic + LCV heuristic

ac3_mrv_lcv_recursion :: Assignment -> CSP -> (Maybe Assignment, Int)
ac3_mrv_lcv_recursion = undefined

 
ac3_mrv_lcv :: CSP -> (Maybe Assignment,Int)
ac3_mrv_lcv csp = ac3_mrv_lcv_recursion [] csp 

-------------------------------------------------
