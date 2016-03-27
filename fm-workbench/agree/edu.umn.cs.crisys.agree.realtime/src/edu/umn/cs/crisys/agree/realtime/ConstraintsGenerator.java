package edu.umn.cs.crisys.agree.realtime;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import org.eclipse.emf.ecore.EObject;
import org.osate.aadl2.Property;
import org.osate.aadl2.instance.ComponentInstance;
import org.osate.aadl2.modelsupport.resources.OsateResourceUtil;
import org.osate.xtext.aadl2.properties.util.EMFIndexRetrieval;
import org.osate.xtext.aadl2.properties.util.PropertyUtils; 

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.Contract;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.Location;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.NodeCallExpr;
import jkind.lustre.TupleExpr;
import jkind.lustre.TupleType;
import jkind.lustre.Type;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;
import jkind.lustre.visitors.ExprIterVisitor;
import jkind.lustre.visitors.ExprMapVisitor;
import jkind.lustre.visitors.PrettyPrintVisitor;

import com.rockwellcollins.atc.agree.analysis.ast.AgreeConnection;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeNode;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeProgram;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeStatement;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeVar;
import com.rockwellcollins.atc.agree.analysis.extentions.AgreeAutomater;
//import com.rockwellcollins.atc.agree.analysis.lustre.visitors.IdGatherer;

	
public class ConstraintsGenerator implements AgreeAutomater{

	private List<AgreeNode> progAsserts;
	
	@Override
	public AgreeProgram transform(AgreeProgram program) {

		boolean test = false;
				
		if (test)
		{
		AgreeNode mTopNode;

		// Make local copies of the final structures that we need to modify
		mTopNode = program.topNode;
		
//		List<AgreeNode> mProgNode = program.agreeNodes;
		progAsserts = new ArrayList<>();
		progAsserts.addAll(program.agreeNodes);
		
		List<Node> lustreNodes = new ArrayList<>();
		lustreNodes.addAll(program.globalLustreNodes);

		// This line needs to go away after making the below if code a function.
		List<AgreeStatement> mT_assertions = new ArrayList<>();
		
		cslNode nNode = new cslNode(mTopNode,true);
		nNode.processNodes();
		mTopNode = nNode.node;
					
		lustreNodes = addCSLNodes(lustreNodes);
		
		// Only add the calendar nodes if at least one calendar type was created.
		mT_assertions.addAll(mTopNode.assertions);
		if (nNode.clkCnt > 0) 
		{
			lustreNodes = buildClkNode(lustreNodes);
			lustreNodes = buildMinNode(lustreNodes);			
			
			// assert (next_inc = (0 -> (pre next2)));
			Expr clkIncrAssertion = new BinaryExpr(new IdExpr("__NEXT_INC"),BinaryOp.EQUAL,new BinaryExpr(new IntExpr(BigInteger.valueOf(0)),BinaryOp.ARROW,new UnaryExpr(UnaryOp.PRE,new  IdExpr(String.join("",nNode.lastSubID,"____NEXT",String.valueOf(nNode.lastSubCnt))))));
			mT_assertions.add(new AgreeStatement("", clkIncrAssertion, null));
				
			// check for 'time'
			for(VarDecl output : mTopNode.outputs)
			{
				if (new String("time").equals(output.id))
				{
					Expr addTime = new BinaryExpr(new IdExpr("time"),BinaryOp.EQUAL,new BinaryExpr(new IntExpr(BigInteger.valueOf(0)),BinaryOp.ARROW,new BinaryExpr(new UnaryExpr(UnaryOp.PRE,new IdExpr("time")),BinaryOp.PLUS,new IdExpr("__NEXT_INC"))));
					mT_assertions.add(new AgreeStatement("", addTime, null));
				}
			}				
		}
//		Property commTimingProp = EMFIndexRetrieval.getPropertyDefinitionInWorkspace(
//				OsateResourceUtil.getResourceSet(), "Timing_Properties::Period");
		  
//		long intVal = PropertyUtils.getIntegerValue(program.topNode.compInst, commTimingProp);
		//PropertyUtils.getEnumLiteral(conn, commTimingProp);
		
		mTopNode = new AgreeNode(program.topNode.id, mTopNode.inputs, mTopNode.outputs, program.topNode.locals, 
				program.topNode.connections, mTopNode.subNodes, mT_assertions, program.topNode.assumptions, 
				program.topNode.guarantees, program.topNode.lemmas, program.topNode.clockConstraint, program.topNode.initialConstraint, 
				program.topNode.clockVar, program.topNode.reference, program.topNode.timing, program.topNode.compInst);
		
		AgreeProgram newProgram = new AgreeProgram(progAsserts, lustreNodes, program.globalTypes, mTopNode);
		
		return newProgram;
		}
		else
			return program;
	}

//	Build the calendar nodes
	private List<Node> buildClkNode(List<Node> lustreNodes)
	{
		List<VarDecl> nInputs = new ArrayList<>();
		List<VarDecl> nOutputs = new ArrayList<>();
		List<VarDecl> nLocals = new ArrayList<>();
		List<Equation> nEquations = new ArrayList<>();
		nInputs.add(new AgreeVar("__PERIOD", NamedType.INT, null, null));
		nInputs.add(new AgreeVar("__PHASE", NamedType.INT, null, null));
		nInputs.add(new AgreeVar("__DRIFT", NamedType.INT, null, null));
		nInputs.add(new AgreeVar("__TTE", NamedType.INT, null, null));
		nInputs.add(new AgreeVar("__NEXT_INC", NamedType.INT, null, null));
		nInputs.add(new AgreeVar("__TMR", NamedType.INT, null, null));
		nInputs.add(new AgreeVar("__PRERUN", NamedType.BOOL, null, null));
		nInputs.add(new AgreeVar("__M_NEXT", NamedType.INT, null, null));
		
		nOutputs.add(new AgreeVar("__NTTE", NamedType.INT, null, null));
		nOutputs.add(new AgreeVar("__FIRED", NamedType.BOOL, null, null));
		nOutputs.add(new AgreeVar("__RUN", NamedType.BOOL, null, null));
		nOutputs.add(new AgreeVar("__RNXT", NamedType.INT, null, null));

		IdExpr period = new IdExpr("__PERIOD");
		IdExpr phase = new IdExpr("__PHASE");
		IdExpr prerun = new IdExpr("__PRERUN");
		IdExpr run = new IdExpr("__RUN");
		IdExpr tte = new IdExpr("__TTE");
		IdExpr drift = new IdExpr("__DRIFT");
		IdExpr tmr = new IdExpr("__TMR");
		IdExpr next_inc = new IdExpr("__NEXT_INC");
		IdExpr fired = new IdExpr("__FIRED");
		IdExpr m_next = new IdExpr("__M_NEXT");
		IdExpr ntte = new IdExpr("__NTTE");

		//		ntte = (if fired then tte else (if (PreRun and (not Run)) then ((period - tte) + drift) else (tmr - next_inc)));
		Expr T1 = new BinaryExpr(prerun,BinaryOp.AND,new UnaryExpr(UnaryOp.NOT,run));
		Expr T2 = new BinaryExpr(new BinaryExpr(period,BinaryOp.MINUS,tte),BinaryOp.PLUS,drift);
		Expr T3 = new BinaryExpr(tmr,BinaryOp.MINUS,next_inc);
		nEquations.add(new Equation(new IdExpr("__NTTE"),new IfThenElseExpr(fired,tte,new IfThenElseExpr(T1,T2,T3))));

//		fired = (Run and (not PreRun));
		nEquations.add(new Equation(new IdExpr("__FIRED"),new BinaryExpr(run,BinaryOp.AND,new UnaryExpr(UnaryOp.NOT,prerun))));

//		Run = (((not PreRun) and ((tmr - next_inc) = 0)) or (PreRun and (not ((tmr - next_inc) = 0))));
		Expr T4 = new BinaryExpr(new BinaryExpr(tmr,BinaryOp.MINUS,next_inc),BinaryOp.EQUAL,new IntExpr(BigInteger.valueOf(0)));
		Expr T5 = new BinaryExpr(new UnaryExpr(UnaryOp.NOT,prerun),BinaryOp.AND,T4);
		Expr T6 = new BinaryExpr(prerun,BinaryOp.AND,new UnaryExpr(UnaryOp.NOT,T4));
		nEquations.add(new Equation(new IdExpr("__RUN"),new BinaryExpr(T5,BinaryOp.OR,T6)));
		
//		r_nxt = (if (m_nxt = (-1)) then ntte else Time_Funcs__min2(m_nxt, ntte));
		Expr T7 = new BinaryExpr(m_next,BinaryOp.EQUAL,new IntExpr(BigInteger.valueOf(-1)));
		Expr T8 = new NodeCallExpr("__MIN2",m_next,ntte);
		nEquations.add(new Equation(new IdExpr("__RNXT"),new IfThenElseExpr(T7,ntte,T8)));
		
		
		lustreNodes.add(new Node("__CLOCK",nInputs,nOutputs,nLocals,nEquations));
		return lustreNodes;
	}

	//	Build the min node
	private List<Node> buildMinNode(List<Node> lustreNodes)
	{
		List<VarDecl> mInputs = new ArrayList<>();
		List<VarDecl> mOutputs = new ArrayList<>();
		List<VarDecl> mLocals = new ArrayList<>();
		List<Equation> mEquations = new ArrayList<>();
		mInputs.add(new AgreeVar("__A", NamedType.INT, null, null));
		mInputs.add(new AgreeVar("__B", NamedType.INT, null, null));

		mOutputs.add(new AgreeVar("__MIN", NamedType.INT, null, null));
		
		IdExpr a = new IdExpr("__A");
		IdExpr b = new IdExpr("__B");
		Expr M1 = new BinaryExpr(a,BinaryOp.LESS,b);
		mEquations.add(new Equation(new IdExpr("__MIN"),new IfThenElseExpr(M1,a,b)));

		lustreNodes.add(new Node("__MIN2",mInputs,mOutputs,mLocals,mEquations));
		return lustreNodes;
	}

	
	private List<Node> addCSLNodes(List<Node> lustreNodes)
	{

		List<Node> nodes = new ArrayList<>();
		nodes.addAll(lustreNodes);

		for (Node node : nodes)
		{
			if (node.id.startsWith("CSL__"))
			{
				lustreNodes.add(updateCSLNode(node));
				lustreNodes.remove(node);
			}
		}
		
		return lustreNodes;
	}
	

	private Node updateCSLNode(Node node)
	{
		List<VarDecl> mInputs = new ArrayList<>();
		List<VarDecl> mOutputs = new ArrayList<>();
		List<VarDecl> mLocals = new ArrayList<>();
		List<Equation> mEquations = new ArrayList<>();
		
		mInputs.addAll(node.inputs);
		mInputs.add(new AgreeVar("T_REMAINING", NamedType.INT, null, null));
		mInputs.add(new AgreeVar("T_EXPIRED", NamedType.INT, null, null));
		mInputs.add(new AgreeVar("CUR_MIN_T_REMAINING", NamedType.INT, null, null));

		mOutputs.addAll(node.outputs);
		mOutputs.add(new AgreeVar("NEXT_T_REMAINING", NamedType.INT, null, null));
		mOutputs.add(new AgreeVar("MIN_T_REMAINING", NamedType.INT, null, null));
		
		// Flip through all the equations for this node and remove any that set our hidden variables to a value.
		for (Equation eq : node.equations)
		{
			for (IdExpr lhs : eq.lhs)
			{
				if (!lhs.id.contentEquals(new String ("T_REMAINING")) && !lhs.id.contentEquals(new String ("T_EXPIRED")) && !lhs.id.contentEquals(new String ("MIN_T_REMAINING")))
					mEquations.add(eq);
			}
		}
//		-- Add a running check for the next min. A -1 resets the calculation
//		r_nxt = if ntr = -1 then m_nxt
//				else if m_nxt = -1 then ntr
//				else if m_nxt <  ntr then m_nxt
//				else ntr;
		Expr T7 = new BinaryExpr(new IdExpr("NEXT_T_REMAINING"),BinaryOp.EQUAL,new IntExpr(BigInteger.valueOf(-1)));
		Expr T8 = new BinaryExpr(new IdExpr("CUR_MIN_T_REMAINING"),BinaryOp.EQUAL,new IntExpr(BigInteger.valueOf(-1)));
		Expr T9 = new NodeCallExpr("__MIN2",new IdExpr("NEXT_T_REMAINING"),new IdExpr("CUR_MIN_T_REMAINING"));
		mEquations.add(new Equation(new IdExpr("MIN_T_REMAINING"),new IfThenElseExpr(T7,new IdExpr("CUR_MIN_T_REMAINING"),new IfThenElseExpr(T8, new IdExpr("NEXT_T_REMAINING"), T9))));
				
		String nodeName = node.id.toString().substring(3);
		return new Node(nodeName,mInputs,mOutputs,mLocals,mEquations);
	}
	
	private void reconcileAssertions(AgreeStatement nAssertion, AgreeStatement oAssertion,String nodeID)
	{
		// We'll search for the exact version of the old string and the replace it with the updated version
		String nTmp = oAssertion.expr.accept(new ExprMapVisitor()).toString();
		
		for (AgreeNode lNode : progAsserts)
		{
			if (lNode.id.equals(nodeID))
			{
				List<AgreeStatement> assertions = new ArrayList<>();
				assertions.addAll(lNode.assertions);
			
				for (AgreeStatement lAssertion : lNode.assertions)
				{
					String lTmp = lAssertion.expr.accept(new ExprMapVisitor()).toString();
			
					if (nTmp.equals(lTmp))
					{
						assertions.add(nAssertion);
						assertions.remove(lAssertion);
						break;
					}
				}
				AgreeNode newNode = new AgreeNode(lNode.id, lNode.inputs, lNode.outputs, lNode.locals, 
						lNode.connections, lNode.subNodes, assertions, lNode.assumptions, 
						lNode.guarantees, lNode.lemmas, lNode.clockConstraint, lNode.initialConstraint, 
						lNode.clockVar, lNode.reference, lNode.timing, lNode.compInst);
				progAsserts.remove(lNode);
				progAsserts.add(newNode);
				break;
			}
		}
		return;
	}
	
	private void reconcileOutputs(List<AgreeVar> outputs,String nodeID)
	{
		for (AgreeNode lNode : progAsserts)
		{
			if (lNode.id.equals(nodeID))
			{
				List<AgreeVar> newOutputs = new ArrayList<>();
				
				for (AgreeVar anOutput : outputs)
				{
					newOutputs.add(anOutput);
				}
				AgreeNode newNode = new AgreeNode(lNode.id, lNode.inputs, newOutputs, lNode.locals, 
						lNode.connections, lNode.subNodes, lNode.assertions, lNode.assumptions, 
						lNode.guarantees, lNode.lemmas, lNode.clockConstraint, lNode.initialConstraint, 
						lNode.clockVar, lNode.reference, lNode.timing, lNode.compInst);
				progAsserts.remove(lNode);
				progAsserts.add(newNode);
				break;
			}
		}
		return;
	}
	
	private class cslNode {
		
		private boolean		topNode;
		private boolean		updated;
		private AgreeNode 	node;
		private int			clkCnt;
		private String		nodeID;
		private String		lastSubID;
		private int	        lastSubCnt;
		private List<AgreeStatement> assertions = new ArrayList<>();
		private List<AgreeVar> outputs = new ArrayList<>();
		private List<AgreeVar> inputs = new ArrayList<>();
		
		public cslNode(AgreeNode origNode, boolean top)
		{
			node = origNode;
			nodeID = origNode.id;
			updated = false;
			topNode = top;
			clkCnt = 0;
			assertions.addAll(origNode.assertions);
			outputs.addAll(node.outputs);
			inputs.addAll(node.inputs);
		}
		
		public void processNodes()
		{
			List<AgreeNode> subnodes = new ArrayList<>(); //Iterator
			List<AgreeNode> newnodes = new ArrayList<>();
			subnodes.addAll(node.subNodes);

			addClocks();
			fixCSLCalls(clkCnt);

			lastSubCnt = 0;
			boolean	firstPass = true;;
			for (AgreeNode node : subnodes)
			{
				cslNode nNode = new cslNode(node,false);
				nNode.processNodes();
				newnodes.add(nNode.node);
				if (nNode.updated)
				{
					if (firstPass) 
					{
						Expr clkIncrAssertion = new BinaryExpr(new IdExpr(nNode.nodeID.concat("____NEXT0")),BinaryOp.EQUAL,new  IdExpr("__NEXT".concat(String.valueOf(clkCnt))));
						assertions.add(new AgreeStatement("", clkIncrAssertion, null));
						firstPass = false;
					}
					else
					{
						Expr clkIncrAssertion = new BinaryExpr(new IdExpr(nNode.nodeID.concat("____NEXT0")),BinaryOp.EQUAL,new  IdExpr(String.join("",lastSubID,"____NEXT",String.valueOf(lastSubCnt))));
						assertions.add(new AgreeStatement("", clkIncrAssertion, null));						
					}

					Expr clkIncrAssertion = new BinaryExpr(new IdExpr(nNode.nodeID.concat("____NEXT_INC")),BinaryOp.EQUAL,new  IdExpr("__NEXT_INC"));
					assertions.add(new AgreeStatement("", clkIncrAssertion, null));						

					// If this is the final subsystem for a system then these two values will be used to create a reference to the minimum next clock 
					// increment that ripples out of all subsystems of this system.
					
					lastSubCnt = nNode.clkCnt;
					lastSubID  = nNode.nodeID;
					updated = true;
				}
			}

			node = new AgreeNode(node.id, inputs, outputs, node.locals, 
					node.connections, newnodes, assertions, node.assumptions, 
					node.guarantees, node.lemmas, node.clockConstraint, node.initialConstraint, 
					node.clockVar, node.reference, node.timing, node.compInst);

			return;
		}
		
		public void fixCSLCalls(int clkStart)
		{
			boolean firstPass = true;
			
			List<AgreeStatement> origAssertions = new ArrayList<>();
			origAssertions.addAll(assertions);
			
			for (AgreeStatement nAssertion : origAssertions)
			{
				String tst = nAssertion.expr.toString();
				if (nAssertion.expr.toString().contains(new String("CSL__")))
				{
					AgreeStatement assertion = updateCSLNodeCall(nAssertion);
					assertions.remove(nAssertion);
					assertions.add(assertion);
					reconcileAssertions(assertion, nAssertion,node.id);
					
					// NEXT_INC is only added once to the outputs. T_REMAINING and NEXT carry the current clkCnt appendage.
					if (firstPass)
					{
						outputs.add(new AgreeVar("__NEXT_INC", NamedType.INT, null, null));
						String newOutput = "__NEXT".concat(String.valueOf(clkCnt));
						if (!existingOutput(newOutput))
						{
							outputs.add(new AgreeVar(newOutput, NamedType.INT, null, null));
						}
						firstPass = false;
						updated = true;
					}
					
					outputs.add(new AgreeVar("__T_REMAIN".concat(String.valueOf(clkCnt)), NamedType.INT, null, null));
					outputs.add(new AgreeVar("__NEXT".concat(String.valueOf(clkCnt+1)), NamedType.INT, null, null));
					clkCnt++;
				}
			}
			
			reconcileOutputs(outputs,node.id);

			return;
		}
		
		private AgreeStatement updateCSLNodeCall(AgreeStatement assertion)
		{					
			List<Expr> mInputs = new ArrayList<>();
			List<Expr> mOutputs = new ArrayList<>();
				
			PrettyPrintVisitor visitor2 = new PrettyPrintVisitor();
			assertion.expr.accept(visitor2);
				
			ExprMapVisitor visitor = new ExprMapVisitor();
			Expr tmp = assertion.expr.accept(visitor);
			Expr tmp2 = ((BinaryExpr) tmp).right;
			Iterator<Expr> iterator = ((NodeCallExpr)tmp2).args.iterator();
			String nodeName = (((NodeCallExpr)tmp2).node.toString()).substring(3);
				
			while (iterator.hasNext()) 
			{
				mInputs.add(iterator.next());
			}
			mInputs.add(new BinaryExpr(new IntExpr(BigInteger.valueOf(-1)),BinaryOp.ARROW,new UnaryExpr(UnaryOp.PRE,new IdExpr("__T_REMAIN".concat(String.valueOf(clkCnt))))));			
			mInputs.add(new IdExpr("__NEXT_INC"));
			if ((topNode) && (clkCnt == 0))
				mInputs.add(new IntExpr(BigInteger.valueOf(-1)));	
			else
				mInputs.add(new IdExpr("__NEXT".concat(String.valueOf(clkCnt))));	
				
				
			tmp2 = ((BinaryExpr) tmp).left;
			mOutputs.addAll(((TupleExpr)tmp2).elements);
			mOutputs.add(new IdExpr("__T_REMAIN".concat(String.valueOf(clkCnt))));			
			mOutputs.add(new IdExpr("__NEXT".concat(String.valueOf(clkCnt+1))));	
			
			Expr tmpExpr = new BinaryExpr(new TupleExpr(mOutputs), BinaryOp.EQUAL, new NodeCallExpr(nodeName,mInputs));
			
			AgreeStatement newAssertion = new AgreeStatement("",tmpExpr,assertion.reference);

			return newAssertion;
		}

		//assert ((tmr1, fired1, run1, next1) = Time_Funcs__periodic_proc(sys1.Period, sys1.Phase, sys1.Drift, sys1.tte, next_inc, (0 -> (pre tmr1)), (false -> (pre run1)), (-1)));

		private  void addClocks()
		{
			for(VarDecl lustreVar : node.outputs)
			{
				AgreeVar var = (AgreeVar)lustreVar;
				if (var.type.toString().endsWith("__Clk_Stat") )
				{
					// The inputs
					IdExpr a = new IdExpr(var.id.concat(".Period"));
					IdExpr b = new IdExpr(var.id.concat(".Phase"));
					IdExpr c = new IdExpr(var.id.concat(".Drift"));
					IdExpr d = new IdExpr(var.id.concat(".tte"));
					IdExpr e = new IdExpr("__NEXT_INC");
					IdExpr f = new IdExpr("__TMR".concat(String.valueOf(clkCnt)));
					IdExpr g = new IdExpr(var.id.concat(".run"));
					
					// The outputs
					List<Expr> ids = new ArrayList<>();
					ids.add(new IdExpr("__TMR".concat(String.valueOf(clkCnt))));
					ids.add(new IdExpr(var.id.concat(".fired")));
					ids.add(new IdExpr(var.id.concat(".run")));
					ids.add(new IdExpr("__NEXT".concat(String.valueOf(clkCnt+1))));
			
					Expr newAssertion;
					if ((clkCnt == 0) && topNode)
					{
						newAssertion = new BinaryExpr(new TupleExpr(ids), BinaryOp.EQUAL,new NodeCallExpr("__CLOCK",a,b,c,d,e,new BinaryExpr(b,BinaryOp.ARROW,new UnaryExpr(UnaryOp.PRE,f)),new BinaryExpr(new BoolExpr(false),BinaryOp.ARROW,new UnaryExpr(UnaryOp.PRE,g)),new IntExpr(BigInteger.valueOf(-1))));
					}	
					else
					{
						newAssertion = new BinaryExpr(new TupleExpr(ids), BinaryOp.EQUAL,new NodeCallExpr("__CLOCK",a,b,c,d,e,new BinaryExpr(b,BinaryOp.ARROW,new UnaryExpr(UnaryOp.PRE,f)),new BinaryExpr(new BoolExpr(false),BinaryOp.ARROW,new UnaryExpr(UnaryOp.PRE,g)),new IdExpr("__NEXT".concat(String.valueOf(clkCnt)))));
					}		

					assertions.add(new AgreeStatement("", newAssertion, null));

					inputs.add(new AgreeVar("__TMR".concat(String.valueOf(clkCnt)), NamedType.INT, null, null));
					inputs.add(new AgreeVar("__RUN".concat(String.valueOf(clkCnt)), NamedType.BOOL, null, null));
					
					clkCnt++;
					inputs.add(new AgreeVar("__NEXT".concat(String.valueOf(clkCnt)), NamedType.INT, null, null));
				}
			}

			return;
		}

		
		private boolean existingOutput(String name)
		{
			boolean found = false;
			
			for (AgreeVar anOutput : outputs)
			{
				if (anOutput.id.equals(name))
				{
					found = true;
					break;
				}
			}
			
			if (!found)
			{
				for (AgreeVar anInput : inputs)
				{
					if (anInput.id.equals(name))
					{
						found = true;
						break;
					}
				}
			}
			return found;
		}
	}

}
