
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
    
    static HashSet <String> forLoopDetection ;
    static int check ;
    static ArrayList < ArrayList<String>> global;
    static String global_query;
    public static void main(String args[])throws IOException
    {
        BufferedReader br = new BufferedReader(new FileReader("input.txt"));
        
        PrintStream out = new PrintStream(new FileOutputStream("output.txt"));
        
        System.setOut(out);
        
        int inputQuery = Integer.parseInt(br.readLine());
        
        List<String> queries = new ArrayList();
        
        for(int i=0;i<inputQuery;i++)
        {
            String temp = br.readLine();
            queries.add(temp.toUpperCase());
            
        }
        LinkedHashMap <String, Data> KB = new LinkedHashMap<String, Data>();
        
        int number_Rules = Integer.parseInt(br.readLine());
                
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
                    
                }
            }

            for(int t=0;t<indicesOfOpeningBraces.size();t++)
            {
                int index = indicesOfOpeningBraces.get(t);
                int start = index+1;

                if(sentence.charAt(start)>=65 && sentence.charAt(start)<=91)
                {
                    
                    while(sentence.charAt(start)!=')' && sentence.charAt(start)!=',')
                    {
                        char temp = Character.toUpperCase(sentence.charAt(start));
                        sentence = sentence.substring(0,start) + temp + sentence.substring(start+1);
                        
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
                    while(sentence.charAt(start)!=')' && sentence.charAt(start)!=',')
                    {
                        char temp = Character.toUpperCase(sentence.charAt(start));
                        sentence = sentence.substring(0,start) + temp + sentence.substring(start+1);
                        
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
                    
                    sentence = sentence.replace(predNameOfPre, predNameOfPre.toUpperCase());
                }
                
                String predicateNameConclusion = extractPredicateName(sentence.split("=>")[1]);
                
                sentence = sentence.replace(predicateNameConclusion, predicateNameConclusion.toUpperCase());
                
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
                
                sentence = sentence.toUpperCase();
                String nameOfPredicate = extractPredicateName(sentence);
                
                
                if(KB.containsKey(nameOfPredicate))
                {
                    
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
                    
                    Data temp = new Data();
                    ArrayList <String> fact = new ArrayList<>();
                    
                    fact.add(sentence);
                    
                    temp.facts = fact;
                    
                    KB.put(nameOfPredicate, temp);
                    
                }
                
            }
                
            
        } 
        
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
            
            
            System.out.println((ans+"").toUpperCase());
        }
        
        
    }
    static boolean  FOL_BC_WITH_UNIFY(LinkedHashMap<String, Data> KB, String curr_goal, String current_Rule)
    {
        curr_goal = curr_goal.trim();
        

        String curr_goal_predicate_name = extractPredicateName(curr_goal);

        check++;

        if(!KB.containsKey(curr_goal_predicate_name))
        {
            
            return false;
        }
        Data rhsFound = KB.get(curr_goal_predicate_name);

        for(String facts:rhsFound.facts)
        {
            if(facts.compareTo(curr_goal)==0)
            {
                
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

            
            global = new ArrayList<>();

            int index1 = curr_goal.indexOf("(");
            int index2 = curr_goal.indexOf((")"));
            String temp = curr_goal.substring(index1+1, index2);
            //System.out.println(temp);

            String argListGoal[] = temp.split(",");
            
            
            

            boolean indexOfVariableConstants[] = new boolean[argListGoal.length];
            
            for(int i=0;i<indexOfVariableConstants.length;i++)
            {
            
                if(argListGoal[i].charAt(0)>=65 && argListGoal[i].charAt(0)<=91)
                {
                    //It is a constant
                    indexOfVariableConstants[i] = true;
                }   
            }

            
            
            
            index1 = conlusion.indexOf("(");
            index2 = conlusion.indexOf((")"));
            String temp2 = conlusion.substring(index1+1, index2);
            

            String argListConclusion[] = temp2.split(",");
            boolean indexOfConstantsInRule[] = new boolean[argListConclusion.length];
            
            for(int i=0;i<indexOfConstantsInRule.length;i++)
            {
            
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
            

            String newConclusion = curr_goal;
            
            ArrayList<String> argsOfNewConclusion = extractArguments(newConclusion.trim());
            
            boolean tempBoolean = true;
            for(int z=0;z<indicesOfVariables.size();z++)
            {
                
                ArrayList <Integer> individualVariable = indicesOfVariables.get(""+(char)(z+97));
                boolean perfectTimes = true;
                if(individualVariable.size()>1)
                {
                        
                        int curr_ind = individualVariable.get(0);
                        
                        String curr_str = argsOfNewConclusion.get(curr_ind);
                        
                        
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
                
                return false;
            }
                
            boolean ruleConstant=true;
            for(int i=0; i<indexOfConstantsInRule.length; i++) {
            	if(indexOfVariableConstants[i] && indexOfConstantsInRule[i]){
            		if(!(argListGoal[i].equals(argListConclusion[i]))){
            			ruleConstant=false;

            			break;
            		}
            	}
            }

            if(!ruleConstant) {
            	continue;
            }
            
            

            for(int i=0;i<indexOfVariableConstants.length;i++)
            {
                
                if(indexOfVariableConstants[i])
                {
                    String toBeSubsituted = argListConclusion[i];

                    rule = rule.replace(toBeSubsituted, argListGoal[i]);
                }

            }
            
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
                continue;
            }
            
            for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
                    String string = entry.getKey();
            
                    ArrayList<String> arrayList = entry.getValue();
                    for(int i=0;i<arrayList.size();i++)
                    {
                        
                    }
                    
                }
            
            if(permu.isEmpty()) {
                
                if(forLoopDetection.contains(rule))
                {
                    return false;
                }
                else
                    forLoopDetection.add(rule);
                
                String splittedRule[] = rule.split("=>");
                
                String premiseString = splittedRule[0].trim();
                
                String allIndividualPremises[] = premiseString.split("\\^");

                int numberOfTruths = 0;
                for(int i=0;i<allIndividualPremises.length;i++)
                {
                    allIndividualPremises[i] = allIndividualPremises[i].trim();

                
                    boolean truthValueOfCurrentPremise = FOL_BC_WITH_UNIFY(KB, allIndividualPremises[i],rule);

                    if(truthValueOfCurrentPremise)
                    {
                        numberOfTruths++;
                    }

                }
                if(numberOfTruths==allIndividualPremises.length)
                {
                    
                    globalTrueOrWala = true;
                    break;

                }
                else
                    continue;

            }
            
            
            for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
                String string = entry.getKey();
                
                ArrayList<String> arrayList = entry.getValue();
                for(int yo=0;yo<arrayList.size();yo++)
                {
                    
                }
                

            }
            

            ArrayList< ArrayList<String>> allStrings = new ArrayList<>();

            for (Map.Entry<String, ArrayList<String>> entry : permu.entrySet()) {
                String string = entry.getKey();
                ArrayList<String> arrayList = entry.getValue();
                allStrings.add(arrayList);

            }

            ArrayList <String> curr2 = new ArrayList<>();
            nested(allStrings.size(), 0, allStrings, curr2);

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
                
            }

            
            for(int i=0;i<returnedHashMaps.size();i++)
            {   
                LinkedHashMap<String, String> timepass = returnedHashMaps.get(i);

                for (Map.Entry<String, String> entry : timepass.entrySet()) {
                    String string = entry.getKey();
                    String string1 = entry.getValue();
                    
                }
                
            }
            
            boolean ekOrEkBooleanForAllSubsitutedConstants = false;

            for(int hashMapsTimes=0;hashMapsTimes<returnedHashMaps.size();hashMapsTimes++)
            {   
                
                String tempRule = rule;
                LinkedHashMap<String, String> timepass = returnedHashMaps.get(hashMapsTimes);

                for (Map.Entry<String, String> entry : timepass.entrySet()) {
                    String string = entry.getKey();
                    String string1 = entry.getValue();
                    
                    tempRule = tempRule.replace(string, string1);

                }
                
                if(forLoopDetection.contains(tempRule))
                {
                    
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

                    
                    boolean truthValueOfCurrentPremise = FOL_BC_WITH_UNIFY(KB, allIndividualPremises[i],tempRule);

                    if(truthValueOfCurrentPremise)
                    {
                        numberOfTruths++;
                    }

                }
                if(numberOfTruths==allIndividualPremises.length)
                {
                    
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


       

    }
    private static LinkedHashMap<String, ArrayList<String>> tryPermutation(LinkedHashMap<String, Data> KB, String rule) {
        
        String splitRule[] = rule.split("=>");
        
        String wholePremise = splitRule[0];
        
        String eachPremise[] = wholePremise.split("\\^");
        LinkedHashMap <String, LinkedHashSet<String> > substi = new LinkedHashMap<String, LinkedHashSet<String>>();
        
        LinkedHashMap <String, ArrayList<String> > listOfAllValuesOfVariables = new LinkedHashMap<>();
        for(int i=0;i<eachPremise.length;i++)
        {
            eachPremise[i] = eachPremise[i].trim();
            
            String argName = extractPredicateName(eachPremise[i]);
            
            ArrayList <String> extractedArg = extractArguments(eachPremise[i]);
            
            
            
            
            Data foundDataFromKB = KB.get(argName);

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
            
            ArrayList <String> list = new ArrayList<>();
            LinkedHashSet<String> set = entry.getValue();
            Iterator<String> iter = set.iterator();
            while (iter.hasNext()) {
                String temp = iter.next();
                list.add(temp);
                    
            }
            listOfAllValuesOfVariables.put(string, list);
                
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
                

                x.add(curr.get(i));
            }
            
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
        
        for (Map.Entry<String, Data> entry : KB.entrySet()) {
            
            
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
