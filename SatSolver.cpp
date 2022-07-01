#include <bits/stdc++.h>
using namespace std;
int variables = 0, clauses = 0;
set < int >satLiterals;

int
maxFrequency (vector < set < int >>&cnf)
{
  //variable with maximum frequency is retured

  int pos[variables + 1], freq[variables + 1];	//pos->frequency of positive terms, freq -> frequency of all terms

  for (int i = 0; i < variables + 1; i++)
    {
      freq[i] = 0;
      pos[i] = 0;
    }

  for (auto it = cnf.begin (); it != cnf.end (); it++)
    {
      for (auto j = it->begin (); j != it->end (); j++)
	{
	  freq[abs (*j)]++;
	  if (*j > 0)
	    pos[*j]++;
	}
    }

  int index = distance (freq, max_element (freq + 1, freq + variables + 1));	//idx will contain index of element with max frequency
  if (2 * pos[index] >= freq[index])
    return index;
  else
    return -index;
}

int
chkPureLit (vector < set < int >>&cnf)
{
  bool arr[2 * variables + 1];	//arr[1..variables] for positive and rest for negative
  for (int i = 0; i < 2 * variables + 1; i++)
    arr[i] = 0;
  for (auto it = cnf.begin (); it != cnf.end (); it++)
    {
      for (auto j = it->begin (); j != it->end (); j++)
	{
	  if (*j > 0)
	    arr[*j] = 1;
	  else
	    arr[variables + abs (*j)] = 1;
	}
    }

  for (int i = 1; i <= variables; i++)
    {
      if ((arr[i] && !arr[variables + i]) || (!arr[i] && arr[variables + i]))
	return 1;
    }

  return 0;
}

set < int >
remPureLiterals (vector < set < int >>&cnf)
{
  bool arr[2 * variables + 1];
  set < int >pure;
  for (int i = 0; i < 2 * variables + 1; i++)
    arr[i] = 0;
  for (auto it = cnf.begin (); it != cnf.end (); it++)
    {
      for (auto j = it->begin (); j != it->end (); j++)
	{
	  if (*j > 0)
	    arr[*j] = 1;
	  else
	    arr[variables + abs (*j)] = 1;
	}
    }

  for (int i = 1; i <= variables; i++)
    {
      //filling set pure

      if (arr[i] && !arr[variables + i])
	pure.insert (i);

      else if (!arr[i] && arr[variables + i])
	pure.insert (-i);
    }

  for (auto it = pure.begin (); it != pure.end (); it++)
    {
      //erasing pure literals from cnf
      int rem = *it;
      cnf.erase (remove_if (cnf.begin (), cnf.end (),[&rem] (set < int >i)
			    {
			    return i.find (rem) != i.end ();}
		 ), cnf.end ());
    }

  return pure;
}

pair < int, int >
chkEmptyClause (vector < set < int >>&cnf)
{
  //check if cnf contain empty clauses
  pair < int, int >check;
  check.first = 0;
  check.second = 0;
  int all = 1;
  for (auto it = cnf.begin (); it != cnf.end (); it++)
    {
      if (it->size () == 0)
	{
	  check.first = 1;
	}

      all = 0;
      if (it->size () == 1)
	{
	  check.second = *((*it).begin ());
	}
    }

  if (all == 1)
    check.first = -1;
  return check;
}

set < int >
rmvSingularClauses (vector < set < int >>&cnf)
{
  // remove clauses with only one literal
  set < int >singular;		//will contain singular clauses
  pair < int, int >check = chkEmptyClause (cnf);
  while (check.first == 0 && check.second != 0)
    {
      for (auto it = cnf.begin (); it != cnf.end (); it++)
	{
	  if (it->size () == 1)
	    singular.insert (*(it->begin ()));
	}

      for (auto iter = singular.begin (); iter != singular.end (); iter++)
	{
	  int rem = *iter;
	  //remove all the singular clauses
	  cnf.erase (remove_if (cnf.begin (), cnf.end (),[&rem] (set < int >i)
				{
				return i.find (rem) != i.end ();}
		     ), cnf.end ());
	  for (auto it = cnf.begin (); it != cnf.end (); it++)
	    {
	      auto it2 = it->find (-rem);
	      if ((it2) != (it->end ()))
		it->erase (it2);
	    }
	}

      check = chkEmptyClause (cnf);
    }

  return singular;
}

int
solve (vector < set < int >>&cnf)
{
  // returns sat or unsat using recursion

  pair < int, int >check = chkEmptyClause (cnf);
  if (check.first == 1)
    return 0;			//if set is empty, it is not satisfiable
  if (check.first == -1)
    return 1;
  if (check.second != 0)
    {
      set < int >q = rmvSingularClauses (cnf);	//all the singular clauses are eliminated

      if (solve (cnf) == 1)
	{
	  for (auto iter = q.begin (); iter != q.end (); iter++)
	    satLiterals.insert (*iter);
	  return 1;
	}
      else
	return 0;
    }

  if (chkPureLit (cnf))
    {
      //if the cnf contains pure literals

      set < int >q = remPureLiterals (cnf);
      if (solve (cnf) == 1)
	{
	  for (auto iter = q.begin (); iter != q.end (); iter++)
	    satLiterals.insert (*iter);
	  return 1;
	}
      else
	return 0;
    }

  int l = maxFrequency (cnf);	//remove max freq literal and check for satisfiabily
  set < int >s1, s2;
  s1.insert (l);
  s2.insert (-l);

  vector < set < int >>copycnf;
  copycnf = cnf;
  copycnf.push_back (s1);

  set < int >q = rmvSingularClauses (copycnf);	//assume literal to be true
  if (solve (copycnf) == 1)
    {
      for (auto iter = q.begin (); iter != q.end (); iter++)
	satLiterals.insert (*iter);
      return 1;
    }
  else
    {
      cnf.push_back (s2);	//assume literal to be false
      q = rmvSingularClauses (cnf);
      if (solve (cnf) == 1)
	{
	  for (auto iter = q.begin (); iter != q.end (); iter++)
	    satLiterals.insert (*iter);
	  return 1;
	}

      return 0;			// unsat if the literal can't be true or false
    }
}

int
main ()
{
  clock_t start = clock ();
  FILE *fp = fopen ("m1.txt", "r");
  fscanf (fp, "p cnf %d %d\n", &variables, &clauses);
  vector < set < int >>cnf;	//store the vector of clauses
  int temp = 0;
  bool arr[2 * variables + 1];	//arr[1...variables]->positive, arr[variable+1...2*variables]->negative

  for (int i = 0; i < 2 * variables + 1; i++)
    arr[i] = false;
  set < int >empty;
  for (int i = 0; i < clauses; i++)
    cnf.push_back (empty);

  for (int i = 0; i < clauses; i++)
    {
      while (1)
	{
	  fscanf (fp, "%d", &temp);
	  //stop if found 0
	  if (temp == 0)
	    break;
	  else if (temp > 0)
	    arr[temp] = true;
	  else
	    arr[variables + abs (temp)] = true;
	  cnf[i].insert (temp);
	}
    }

  for (int i = 1; i <= variables; i++)
    {
      //remove pure literals

      if (arr[i] && !arr[variables + i])
	{
	  satLiterals.insert (i);
	  cnf.erase (remove_if (cnf.begin (), cnf.end (),[&i] (set < int >j)
				{
				return j.find (i) != j.end ();}
		     ), cnf.end ());
	}
      else if (!arr[i] && arr[variables + i])
	{
	  satLiterals.insert (-i);
	  cnf.erase (remove_if (cnf.begin (), cnf.end (),[&i] (set < int >j)
				{
				return j.find (-i) != j.end ();}
		     ), cnf.end ());
	}
    }

  for (int i = 1; i <= variables; i++)
    {
      //remove literal 'a' and '-a'

      for (auto it = cnf.begin (); it != cnf.end ();)
	{
	  if (it->find (i) != it->end () && it->find (-i) != it->end ())
	    it = cnf.erase (it);
	  else
	    it++;
	}
    }

  set < int >q = rmvSingularClauses (cnf);	//unit propagation

  if (solve (cnf))
    {
      //check if the clauses are satisfiable
      printf ("SAT\n\n");
      for (auto iter = q.begin (); iter != q.end (); iter++)
	satLiterals.insert (*iter);
      printf ("MODEL\n");
      for (int i = 1; i <= variables; i++)
	{
	  if (satLiterals.find (i) != satLiterals.end ())
	    printf ("%d ", i);
	  else if (satLiterals.find (-i) != satLiterals.end ())
	    printf ("%d ", -i);
	  else
	    printf ("%d ", i);
	}

      printf ("\n\n");
    }
  else
    printf ("UNSAT\n");
  printf ("*******Time=%f********\n",
	  ((double) (clock () - start) / 10.0) / CLOCKS_PER_SEC);
  fclose (fp);
  return 0;
}
