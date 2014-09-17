/**
 * 
 */
package edu.umn.cs.crisys.smaccm.aadl2rtos.codegen.CAmkES;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import edu.umn.cs.crisys.smaccm.aadl2rtos.Aadl2RtosException;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.dispatcher.Dispatcher;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.dispatcher.ExternalHandler;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.dispatcher.IRQDispatcher;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.dispatcher.InputEventDispatcher;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.dispatcher.PeriodicDispatcher;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.port.OutputEventPort;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.thread.Connection;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.thread.OutgoingDispatchContract;
import edu.umn.cs.crisys.smaccm.aadl2rtos.model.type.UnitType;

/**
 * @author Whalen
 *
 */
public class DispatcherNames {
  Dispatcher dp; 
  
  DispatcherNames(Dispatcher dp) {
    this.dp = dp;
  }
  
  //////////////////////////////////////////////////////////////////////
  //
  // root port name
  // 
  //////////////////////////////////////////////////////////////////////

  public String getName() {
    return dp.getName();
  }
  
  //////////////////////////////////////////////////////////////////////
  //
  // query functions.
  //
  //////////////////////////////////////////////////////////////////////

  public boolean getHasData() {
    return !(dp.getType() instanceof UnitType); 
  }
  
  public boolean getIsPeriodic() {
    return (dp instanceof PeriodicDispatcher);
  }
  
  public boolean getIsIRQ() {
    return (dp instanceof IRQDispatcher); 
  }

  public boolean getIsInput() {
    return (dp instanceof InputEventDispatcher); 
  }
  public boolean getIsEvent() {
    return (getIsInput()) &&
         !((InputEventDispatcher)dp).getEventPort().hasData(); 
  }
  
  public boolean getIsEventData() {
    return (getIsInput()) &&
        ((InputEventDispatcher)dp).getEventPort().hasData(); 
  }

  //////////////////////////////////////////////////////////
  //
  // Constructors for name classes related to port
  // 
  //////////////////////////////////////////////////////////
  
  public List<ExternalHandlerNames> getExternalHandlers() {
     List<ExternalHandlerNames> ehl = new ArrayList<>(); 
     for (ExternalHandler eh : dp.getExternalHandlerList()) {
       ehl.add(new ExternalHandlerNames(eh)); 
     }
     return ehl;
  }
  
  public OutgoingDispatchContractNames getMaxDispatchContracts() {
    OutgoingDispatchContract odc = 
        OutgoingDispatchContract.maxDispatcherUse(dp.getDispatchLimits());
    OutgoingDispatchContractNames odcNames = new OutgoingDispatchContractNames(odc); 
    return odcNames;
  }
  
  public List<DispatchContractNames> getContracts() {
    OutgoingDispatchContract odc = 
        OutgoingDispatchContract.maxDispatcherUse(dp.getDispatchLimits());
    List<DispatchContractNames> pdl = new ArrayList<>(); 
    for (Map.Entry<OutputEventPort, Integer> elem : odc.getContract().entrySet()) {
      pdl.add(new DispatchContractNames(elem));
    }
    return pdl;
    
  }
  
  public PortNames getInputEventDispatcherPort() {
    if (dp instanceof InputEventDispatcher) {
      PortNames port = new PortNames(((InputEventDispatcher) dp).getEventPort());
      return port;
    } else {
      throw new Aadl2RtosException("getInputEventDispatcherPort() : dispatcher is not an input event dispatcher");
    }
  }
  
  public TypeNames getType() {
    return new TypeNames(dp.getType());
  }

  public ThreadImplementationNames getThreadImplementation() {
    return new ThreadImplementationNames(dp.getOwner());
  }

  //////////////////////////////////////////////////////////
  //
  // Var names for global variables related to dispatcher
  // 
  //////////////////////////////////////////////////////////
  

  public String getDispatchOccurredVar() {
    return "smaccm_occurred_" + getName(); 
  }
  
  public String getPeriodicTimeVar() {
    return "smaccm_time_" + getName(); 
  }
  
  
  public String getIdlDispatcherName() {
    return "dispatch_" + getName(); 
  }
  
  //////////////////////////////////////////////////////////
  //
  // Function names related to dispatcher
  // 
  //////////////////////////////////////////////////////////

  public String getDispatcherComponentDispatchName() {
    ThreadImplementationNames tin = new ThreadImplementationNames(dp.getOwner());
    return tin.getNormalizedName() + "_" + dp.getName();
  }
  
  // NOTE: for getDispatcherCFileDispatcherFnName, value returned must 
  // be the same as PortNames::getDispatcherName(); 
  // That is why the custom case with getIsInput().

  public String getDispatcherCFileDispatcherFnName() {
    if (getIsInput()) {
      return this.getInputEventDispatcherPort().getDispatcherCFileDispatcherFnName(); 
    } else {
      return "smaccm_dispatcher_" + getName();
    }
  }

  public String getCamkesRPCDispatchFnName() {
    TypeNames type = new TypeNames(dp.getType());
    return (getDispatcherCFileDispatcherFnName()) + "_" + type.getWriterFn();
  }

  //////////////////////////////////////////////////////////
  //
  // Param/stmt/FnCall writers related to this port.
  // 
  //////////////////////////////////////////////////////////

  public String getNameAsOutputParam() {
    TypeNames tyn = new TypeNames(dp.getType());
    return tyn.getOutputTypeName() + " " + getName();
  }
  
  public String getNameAsInputParam() {
    TypeNames tyn = new TypeNames(dp.getType());
    return tyn.getInputTypeName() + " " + getName();
  }
  
  public String getInputDispatcherIsEmptyFnCall() {
    return this.getInputEventDispatcherPort().getIsEmptyFnCall(); 
  }
                   
  public String getPassiveComponentDispatcherPathName() {
    return this.getThreadImplementation().getInterfaceInstanceName() + "_" + 
        this.getIdlDispatcherName(); 
  }
  
};




