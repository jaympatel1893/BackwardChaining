/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package assignment.pkg3;
/**
 *
 * @author jay
 */

import java.io.*;
import java.util.*;

class Data{
    
    ArrayList <String> facts = new ArrayList<>();
    ArrayList <String> rules = new ArrayList<>();
    
}

public class inference
{
    
    static HashSet <String> forLoopDetection ;//= new HashSet<String>();
    static int check ;
    static ArrayList < ArrayList<String>> global;// = new ArrayList<>();
    static String global_query;
    public static void main(String args[])throws IOException
    {
        BufferedReader br = new BufferedReader(new FileReader("/Users/jay/NetBeansProjects/Assignment 3/src/assignment/pkg3/input_1.txt"));
        //BufferedReader br = new BufferedReader(new FileReader(args[1]));
        //PrintStream out = new PrintStream(new FileOutputStream("output.txt"));
        
        //System.setOut(out);
        
        int inputQuery = Integer.parseInt(br.readLine());
        
        List<String> queries = new ArrayList();
        
        for(int i=0;i<inputQuery;i++)
        {
            String temp = br.readLine();
            queries.add(temp.toUpperCase());
            //System.out.println(queries.get(i));
        }
        LinkedHashMap <String, Data> KB = new LinkedHashMap<String, Data>();
        
        int number_Rules = Integer.parseInt(br.readLine());
//        System.out.println("Hello");
//        System.out.println(number_Rules);
        //List<Term> terms = new ArrayList<Term>();
        
        HashSet <String> allPredicateNames = new HashSet<String>();
        
        for(int i=0;i<number_Rules;i++)
        {
            String sentence = br.readLine();
            
            
            ArrayList<Integer> indicesOfOpeningBraces = new ArrayList<>();
            ArrayList<Integer> indicesOfComma = new ArrayList<>();

            for(int t=0;t<sentence.length();t++)
            {
                if(sentence.charAt(t)=='(')
                {
                    indicesOfOpeningBraces.add(t);

                }
                if(sentence.charAt(t)==',')
                {
                    indicesOfComma.add(t);
                    //System.out.println(i);
                }
            }

            for(int t=0;t<indicesOfOpeningBraces.size();t++)
            {
                int index = indicesOfOpeningBraces.get(t);
                int start = index+1;

                if(sentence.charAt(start)>=65 && sentence.charAt(start)<=91)
                {
                    //Its is a constant
                    //System.out.println("Aya");
                    //whileloop till ) or ,
                    while(sentence.charAt(start)!=')' && sentence.charAt(start)!=',')
                    {
                        char temp = Character.toUpperCase(sentence.charAt(start));
                        sentence = sentence.substring(0,start) + temp + sentence.substring(start+1);
                        //System.out.println("hmm "+sentence);
                        start++;
                    }
                }
            }
            for(int t=0;t<indicesOfComma.size();t++)
            {
                int index = indicesOfComma.get(t);
                int start = index+1;

                if(sentence.charAt(start)>=65 && sentence.charAt(start)<=91)
                {
                    //Its is a constant
                    //System.out.println("Aya");
                    //whileloop till ) or ,
                    while(sentence.charAt(start)!=')' && sentence.charAt(start)!=',')
                    {
                        char temp = Character.toUpperCase(sentence.charAt(start));
                        sentence = sentence.substring(0,start) + temp + sentence.substring(start+1);
                        //System.out.println("hmm "+sentence);
                        start++;
                    }
                }
            }
            
            if(sentence.contains("=>"))
            {
                //It is a rule
                
                String temp_terms[] = sentence.split("=>");
                
                String con = temp_terms[1].trim();
                
                String pre[] = temp_terms[0].split("\\^");
                
                for(int j=0;j<pre.length;j++)
                {
                    String predNameOfPre = extractPredicateName(pre[j]);
                    //System.out.println(predNameOfPre);
                    sentence = sentence.replace(predNameOfPre, predNameOfPre.toUpperCase());
                }
                
                String predicateNameConclusion = extractPredicateName(sentence.split("=>")[1]);
                //System.out.println("LODU"+sentence);
                sentence = sentence.replace(predicateNameConclusion, predicateNameConclusion.toUpperCase());
                //System.out.println("Madarchod" +predicateNameConclusion +" " + sentence);
                predicateNameConclusion = predicateNameConclusion.toUpperCase();
                
                if(KB.containsKey(predicateNameConclusion))
                {
                    Data temp = KB.get(predicateNameConclusion);
                    
                    temp.rules.add(sentence);
                    
                }
                else
                {
                    Data newData = new Data();
                    
                    newData.rules.add(sentence);
                    
                    KB.put(predicateNameConclusion, newData);
                }
            }
            else
            {
                //It is a fact
                sentence = sentence.toUpperCase();
                String nameOfPredicate = extractPredicateName(sentence);
                
                //When it is a fact and string was already present inside the hashmap
                if(KB.containsKey(nameOfPredicate))
                {
                    //No need to add new key value
                    //get the data value from the hashmap
                    
                    //find the data which was already inside the hashmap
                    for (Map.Entry<String, Data> entry : KB.entrySet()) {
                        String string = entry.getKey();
                        if(string.compareTo(nameOfPredicate)==0)
                        {
                            Data data = entry.getValue();
                            data.facts.add(sentence);
                        }
                    }
                }
                else
                {
                    //When you encounter this fact as totally new one
                    Data temp = new Data();
                    ArrayList <String> fact = new ArrayList<>();
                    
                    fact.add(sentence);
                    
                    temp.facts = fact;
                    
                    KB.put(nameOfPredicate, temp);
                    
                }
                
            }
                
            
        } 
        //printKB(KB);
        //System.out.println("Start Queries");
        for(String goal: queries)
        {
            forLoopDetection = new HashSet<>();
            forLoopDetection.add(goal);
            check = 0;
            global_query = goal;
            boolean ans;
            try{
                ans = FOL_BC_WITH_UNIFY(KB, goal, goal);         
            }
            catch(StackOverflowError e)
            {
                System.out.println("FALSE");
                continue;
            }
            catch(Exception e)
            {
                System.out.println("FALSE");
                continue;
            }
            
            //System.out.println(goal+" answer "+ ans);
            System.out.println((ans+"").toUpperCase());
        }
        
        
    }
    static boolean  FOL_BC_WITH_UNIFY(LinkedHashMap<String, Data> KB, String curr_goal, String current_Rule)
    {
        curr_goal = curr_goal.trim();
        //System.out.println("Current goal is:"+curr_goal);

        String curr_goal_predicate_name = extractPredicateName(curr_goal);
//        if(forLoopDetection.contains(curr_goal) && check!=0)
//        {
//            System.out.println("Infi Loop");
//            forLoopDetection = new HashSet<>();
//            
//            check = 0;
//            
//            forLoopDetection.add(global_query);
//            //forLoopDetection.add("A(BOB)");
//            return false;
//        }
//        if(check>0)
//        {
//            forLoopDetection.add(curr_goal);
//        }
        check++;

        if(!KB.containsKey(curr_goal_predicate_name))
        {
            //System.out.println("RHS me hai hi nahi hence False");
            return false;
        }
        Data rhsFound = KB.get(curr_goal_predicate_name);

        for(String facts:rhsFound.facts)
        {
            if(facts.compareTo(curr_goal)==0)
            {
                //System.out.println("Direct fact mila hence true"+curr_goal);
                forLoopDetection.remove(current_Rule);
                return true;
            }

        }
        //Loop condtion remains
        //if not any of the above base cases, split premises and recurse again
        boolean globalTrueOrWala = false;

        for(String rule: rhsFound.rules)
        {
            //For every rule find if its possible to get a true
            //rule can be of the form = "A(x)^B(x,y)=>C(x,y)";

            String splitRule[] = rule.split("=>");
            
            

            //Get the rhs of the rule
            String conlusion = splitRule[1];
            
            

            //String goal = "C(Bob,y)";

            global = new ArrayList<>();

            int index1 = curr_goal.indexOf("(");
            int index2 = curr_goal.indexOf((")"));
            String temp = curr_goal.substring(index1+1, index2);
            //System.out.println(temp);

            String argListGoal[] = temp.split(",");
            
            
            //System.out.println("BC"+Arrays.toString(argListGoal));

            boolean indexOfVariableConstants[] = new boolean[argListGoal.length];
            //System.out.println(indexOfVariableConstants.length);
            //false means not a constant
            for(int i=0;i<indexOfVariableConstants.length;i++)
            {
                //System.out.println(argListGoal[i].charAt(0));
                if(argListGoal[i].charAt(0)>=65 && argListGoal[i].charAt(0)<=91)
                {
                    //It is a constant
                    indexOfVariableConstants[i] = true;
                }   
            }

            //conclusion ka arguments
            
            
            index1 = conlusion.indexOf("(");
            index2 = conlusion.indexOf((")"));
            String temp2 = conlusion.substring(index1+1, index2);
            //System.out.println(temp2);

            String argListConclusion[] = temp2.split(",");
            boolean indexOfConstantsInRule[] = new boolean[argListConclusion.length];
            
            for(int i=0;i<indexOfConstantsInRule.length;i++)
            {
                //System.out.println(argListGoal[i].charAt(0));
                if(argListConclusion[i].charAt(0)>=65 && argListConclusion[i].charAt(0)<=91)
                {
                    //It is a constant
                    indexOfConstantsInRule[i] = true;
                }   
            }
            
            LinkedHashMap <String, Integer> possibleSubs = new LinkedHashMap<>();
            LinkedHashMap <String, ArrayList<Integer> > indicesOfVariables = new LinkedHashMap<>();
            
            for(int chars = 0;chars<26;chars++)
            {
                possibleSubs.put(""+(char)(chars+97), 0);
                indicesOfVariables.put(""+(char)(chars+97), new ArrayList<>());
            }
            for(int k = 0;k<argListConclusion.length;k++)
            {
                
                if(argListConclusion[k].charAt(0)>=97 && argListConclusion[k].charAt(0)<=123)
                {
                    
                    int curr_value = possibleSubs.get(""+argListConclusion[k].charAt(0));
                    curr_value++;
                    possibleSubs.put(""+(char)argListConclusion[k].charAt(0), curr_value);
                    
                    
                    ArrayList<Integer> repeatingInd = indicesOfVariables.get(""+argListConclusion[k].charAt(0));
                    repeatingInd.add(k);
                    
                    indicesOfVariables.put(""+(char)argListConclusion[k].charAt(0), repeatingInd);

                }
            }
            
//            for (Map.Entry<String, ArrayList<Integer>> entry : indicesOfVariables.entrySet()) {
//                String string = entry.getKey();
//                System.out.println(string);
//                ArrayList<Integer> integer = entry.getValue();
//                for(int i=0;i<integer.size();i++)
//                {
//                    System.out.print(integer.get(i)+" ");
//                }
//                
//                System.out.println("");
//            }
            String newConclusion = curr_goal;
            
            ArrayList<String> argsOfNewConclusion = extractArguments(newConclusion.trim());
            
//            for(String t : argsOfNewConclusion)
//            {
//                System.out.println(t);
//            }
//            for(String t: argListConclusion)
//            {
//                System.out.println(t);
//            }
//            for (Map.Entry<String, ArrayList<Integer>> entry : indicesOfVariables.entrySet()) {
//                String string = entry.getKey();
//                System.out.println("String"+string);
//                ArrayList<Integer> arrayList = entry.getValue();
//                for(int i=0;i<arrayList.size();i++)
//                {
//                    System.out.println(arrayList.get(i));
//                }
//                
//            }
            
            
            boolean tempBoolean = true;
            for(int z=0;z<indicesOfVariables.size();z++)
            {
                
                ArrayList <Integer> individualVariable = indicesOfVariables.get(""+(char)(z+97));
                boolean perfectTimes = true;
                if(individualVariable.size()>1)
                {
                        
                        //System.out.println("Yes");
                        int curr_ind = individualVariable.get(0);
                        //System.out.println("curr index is"+curr_ind);
                        String curr_str = argsOfNewConclusion.get(curr_ind);
                        //System.out.println("curr str"+curr_str);
                        
                        for(int z2 = 1;z2<individualVariable.size();z2++)
                        {
                            if(!argsOfNewConclusion.get(individualVariable.get(z2)).equals(curr_str))
                            {
                                perfectTimes = false;
                                break;
                            }
                        }
                }
                if(!perfectTimes)
                {
                    tempBoolean = false;
                    break;
                }
            }
            if(!tempBoolean)
            {
                //System.out.println("Locha e ulfat");
                return false;
            }
                
            boolean ruleConstant=true;
            for(int i=0; i<indexOfConstantsInRule.length; i++) {
            	if(indexOfVariableConstants[i] && indexOfConstantsInRule[i]){
            		if(!(argListGoal[i].equals(argListConclusion[i]))){
            			ruleConstant=false;
            			//System.out.println(rule + ArgumentListOfGoal[i] + argumentListOfConclusion[i] + goal);
            			break;
            		}
            	}
            }

            if(!ruleConstant) {
            	continue;
            }
            
            

            for(int i=0;i<indexOfVariableConstants.length;i++)
            {
                //System.out.println(indexOfVariableConstants[i]);
                if(indexOfVariableConstants[i])
                {
                    String toBeSubsituted = argListConclusion[i];

                    rule = rule.replace(toBeSubsituted, argListGoal[i]);
                }

            }
            //System.out.println("Rule ye hai"+rule);
            
            
            

            //There is a possibility that this rule on LHS has still some variables

            //We have to substitute all possible values of variables

            //Now split all premises if there is ^

            //do something which changes rule into only constants, so that when you call recursively, your goal will not have any variables
            LinkedHashMap <String, ArrayList<String> > permu = new LinkedHashMap<>();
            try{
                 permu = tryPermutation(KB, rule);
            
            }
            catch(Exception e)
            {
                
//                for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
//                    String string = entry.getKey();
//                    System.out.println(string);
//                    ArrayList<String> arrayList = entry.getValue();
//                    for(int i=0;i<arrayList.size();i++)
//                    {
//                        System.out.print(arrayList.get(i));
//                    }
//                    
//                }
//                System.out.println("No Subs");
                
                continue;
            }
            //System.out.println("Permu size"+permu.size());
            for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
                    String string = entry.getKey();
              //      System.out.println(string);
                    ArrayList<String> arrayList = entry.getValue();
                    for(int i=0;i<arrayList.size();i++)
                    {
                //        System.out.print(arrayList.get(i));
                    }
                    
                }
            
            if(permu.isEmpty()) {
                
                if(forLoopDetection.contains(rule))
                {
                    return false;
                }
                else
                    forLoopDetection.add(rule);
                //System.out.println("Hah" + rule);
                String splittedRule[] = rule.split("=>");
                
                //You get the entire LHS here
                String premiseString = splittedRule[0].trim();
                //Now split lhs with ^ and now every term now is called recursively
                //before that trim all terms
                String allIndividualPremises[] = premiseString.split("\\^");

                int numberOfTruths = 0;
                for(int i=0;i<allIndividualPremises.length;i++)
                {
                    allIndividualPremises[i] = allIndividualPremises[i].trim();

                    //System.out.println("Bhosdina "+allIndividualPremises[i]);
                    boolean truthValueOfCurrentPremise = FOL_BC_WITH_UNIFY(KB, allIndividualPremises[i],rule);

                    if(truthValueOfCurrentPremise)
                    {
                        numberOfTruths++;
                    }

                }
                if(numberOfTruths==allIndividualPremises.length)
                {
                    //Ek bhi rule ka sab true aya to khatam return true karna hai and baki ke rules me dhundne ka jaroori nahi
                    //so you can break here
                    globalTrueOrWala = true;
                    break;

                }
                else
                    continue;

            }
            
            //This hashmap has all possible values of variables in the above rule
            //System.out.println("Permu is:");
            for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
                String string = entry.getKey();
                //System.out.print(string+"=>");
                ArrayList<String> arrayList = entry.getValue();
                for(int yo=0;yo<arrayList.size();yo++)
                {
                    //System.out.print(arrayList.get(yo)+" ");
                }
                //System.out.println("");

            }
            //String ruleTriedPermutation = 

            ArrayList< ArrayList<String>> allStrings = new ArrayList<>();

            for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
                String string = entry.getKey();
                ArrayList<String> arrayList = entry.getValue();
                allStrings.add(arrayList);

            }

            ArrayList <String> curr2 = new ArrayList<>();
            nested(allStrings.size(), 0, allStrings, curr2);

            //System.out.println("hahahaha Strings");
            //System.out.println(global.size());

            ArrayList < LinkedHashMap<String, String>  > returnedHashMaps = new ArrayList<>();


            for(int i=0;i<global.size();i++)
            {
                LinkedHashMap<String, String> oneHashMap = new LinkedHashMap<>();
                int count = 0;
                for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
                    String string = entry.getKey();

                    oneHashMap.put(string, global.get(i).get(count++));

                }
                returnedHashMaps.add(oneHashMap);
                //System.out.println();
            }

            //System.out.println("Finally");
            for(int i=0;i<returnedHashMaps.size();i++)
            {   
                LinkedHashMap<String, String> timepass = returnedHashMaps.get(i);

                for (Map.Entry<String, String> entry : timepass.entrySet()) {
                    String string = entry.getKey();
                    String string1 = entry.getValue();
                    //System.out.print(string);
                    //System.out.print(string1);

                }
                //System.out.println("");
            }
            //Now I have returnedHashMap which is array of substitutions
            boolean ekOrEkBooleanForAllSubsitutedConstants = false;

            for(int hashMapsTimes=0;hashMapsTimes<returnedHashMaps.size();hashMapsTimes++)
            {   
                
                String tempRule = rule;
                LinkedHashMap<String, String> timepass = returnedHashMaps.get(hashMapsTimes);

                for (Map.Entry<String, String> entry : timepass.entrySet()) {
                    String string = entry.getKey();
                    String string1 = entry.getValue();
                    //System.out.print(string);
                    //System.out.print(string1);
                    tempRule = tempRule.replace(string, string1);

                }
                
                if(forLoopDetection.contains(tempRule))
                {
                    //System.out.println("idhar");
                    return false;
                }
                else
                {
                    
                    forLoopDetection.add(tempRule);
                }

                String splittedRule[] = tempRule.split("=>");

                //You get the entire LHS here
                String premiseString = splittedRule[0].trim();
                //Now split lhs with ^ and now every term now is called recursively
                //before that trim all terms
                String allIndividualPremises[] = premiseString.split("\\^");

                int numberOfTruths = 0;
                for(int i=0;i<allIndividualPremises.length;i++)
                {
                    allIndividualPremises[i] = allIndividualPremises[i].trim();

                    //System.out.println("Bhosdina "+allIndividualPremises[i]);
                    boolean truthValueOfCurrentPremise = FOL_BC_WITH_UNIFY(KB, allIndividualPremises[i],tempRule);

                    if(truthValueOfCurrentPremise)
                    {
                        numberOfTruths++;
                    }

                }
                if(numberOfTruths==allIndividualPremises.length)
                {
                    //Ek bhi rule ka sab true aya to khatam return true karna hai and baki ke rules me dhundne ka jaroori nahi
                    //so you can break here
                    globalTrueOrWala = true;
                    break;

                }
                else
                    continue;

            }

            if(globalTrueOrWala)
                break;

        }
        if(globalTrueOrWala)
            return true;

        return false;


        //remove in the end this return 
        //return false;


    }
    private static LinkedHashMap<String, ArrayList<String>> tryPermutation(LinkedHashMap<String, Data> KB, String rule) {
        //First of all split the rule
        //System.out.println(rule);
        //System.out.println(rule);
        String splitRule[] = rule.split("=>");
        //System.out.println(Arrays.toString(splitRule));
        String wholePremise = splitRule[0];
        
        String eachPremise[] = wholePremise.split("\\^");
        LinkedHashMap <String, LinkedHashSet<String> > substi = new LinkedHashMap<String, LinkedHashSet<String>>();
        
        LinkedHashMap <String, ArrayList<String> > listOfAllValuesOfVariables = new LinkedHashMap<>();
        for(int i=0;i<eachPremise.length;i++)
        {
            eachPremise[i] = eachPremise[i].trim();
            
            String argName = extractPredicateName(eachPremise[i]);
            
            ArrayList <String> extractedArg = extractArguments(eachPremise[i]);
            
            //System.out.println(argName);
            
            
            Data foundDataFromKB = KB.get(argName);
//            System.out.println("haha");
//            for (Map.Entry<String, Data> entry : KB.entrySet()) {
//                String string = entry.getKey();
//                Data d = entry.getValue();
//                System.out.println(string);
//                
//                
//            }
            
//            if(foundDataFromKB==null)
//                System.out.println("null");
            
            ArrayList <String> facts = foundDataFromKB.facts;
            
            
            boolean constants[] = new boolean[extractedArg.size()];
            int counter1 = 0;
            for(int j=0;j<extractedArg.size();j++)
            {
                if(extractedArg.get(j).charAt(0)>=65 && extractedArg.get(j).charAt(0)<=91)
                {
                    constants[j] = true;
                    counter1++;
                }
            }
            
            for(int times = 0;times<facts.size();times++)
            {
                ArrayList <String> argumentsFacts = extractArguments(facts.get(times));
                int counter2 = 0;
                for(int j=0;j<constants.length;j++)
                {
                    if(constants[j])
                    {
                        //it is a constant
                        String constantFromRule = extractedArg.get(j);

                        String constantFromFact = argumentsFacts.get(j);

                        if(constantFromFact.compareTo(constantFromRule)==0)
                        {
                            counter2++;
                        }

                    }
                }

                if(counter1==counter2)
                {
                    //System.out.println("rule and fact match");

                    for(int j=0;j<constants.length;j++)
                    {
                        if(!constants[j])
                        {
                            String variableFromRule = extractedArg.get(j);

                            String constantFromFact = argumentsFacts.get(j);

                            if(!substi.containsKey(variableFromRule))
                            {
                                LinkedHashSet <String> temp = new LinkedHashSet<>();

                                temp.add(constantFromFact);

                                substi.put(variableFromRule, temp);
                            }
                            else
                            {
                                LinkedHashSet<String> temp = substi.get(variableFromRule);

                                temp.add(constantFromFact);

                            }

                        }
                    }
                }
            }
            
        }
        for (Map.Entry<String, LinkedHashSet<String>> entry : substi.entrySet()) {

            String string = entry.getKey();
            //System.out.print(string+" ");
            
            ArrayList <String> list = new ArrayList<>();
            LinkedHashSet<String> set = entry.getValue();
            Iterator<String> iter = set.iterator();
            while (iter.hasNext()) {
                String temp = iter.next();
                list.add(temp);
                //System.out.println(iter.next());
            }
            listOfAllValuesOfVariables.put(string, list);
            //System.out.println();
        }
        return listOfAllValuesOfVariables;
        
        
        
    }
    
    static void nested(int depth, int index, ArrayList< ArrayList<String> > list, ArrayList<String> curr)
    {

        if(depth==0)
        {


            ArrayList <String> x = new ArrayList<>();
            int i;
            for( i=0;i<curr.size();i++)
            {
                //System.out.print(curr.get(i)+" ");

                x.add(curr.get(i));
            }
            //System.out.println("");
            global.add(x);
            
        }
        else
        {
            for(int i=0;i<list.get(index).size();i++)
            {

                curr.add(list.get(index).get(i));

                nested(depth-1, index+1, list, curr);
                
                curr.remove(curr.size()-1);
                
            }
        }

    }
    
    static void printKB(HashMap<String, Data> KB)
    {
        //System.out.println("Idhar Haha");
        //System.out.println("Printing KB");
        for (Map.Entry<String, Data> entry : KB.entrySet()) {
            
            //System.out.println("hahaha");
            String string = entry.getKey();
            
            System.out.println(string);
            
            Data data = entry.getValue();
            System.out.println("Facts:");
            for(String fact: data.facts)
            {
                System.out.println(fact);
            }
            System.out.println("Rules");
            for(String rule: data.rules)
            {
                System.out.println(rule);
            }
            
        }
    }
    static String extractPredicateName(String term)
    {
        int index = term.indexOf("(");
        
        return term.substring(0, index).trim();
    }
    static ArrayList<String> extractArguments(String term)
    {
        ArrayList <String> extractedArg = new ArrayList<String>();
        
        int startingIndex = term.indexOf("(");
        
        int endingIndex = term.indexOf(")");
        
        String Arguments = term.substring(startingIndex+1, endingIndex);
        
        String argArray[] = Arguments.split(",");
        
        for(int i=0;i<argArray.length;i++)
        {
            extractedArg.add(argArray[i].trim());
        }
        return extractedArg;   
    }
}
