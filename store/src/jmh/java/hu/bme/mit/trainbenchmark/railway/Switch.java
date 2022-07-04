/**
 */
package hu.bme.mit.trainbenchmark.railway;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Switch</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link hu.bme.mit.trainbenchmark.railway.Switch#getCurrentPosition <em>Current Position</em>}</li>
 *   <li>{@link hu.bme.mit.trainbenchmark.railway.Switch#getPositions <em>Positions</em>}</li>
 * </ul>
 *
 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getSwitch()
 * @model
 * @generated
 */
public interface Switch extends TrackElement {
	/**
	 * Returns the value of the '<em><b>Current Position</b></em>' attribute.
	 * The literals are from the enumeration {@link hu.bme.mit.trainbenchmark.railway.Position}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Current Position</em>' attribute.
	 * @see hu.bme.mit.trainbenchmark.railway.Position
	 * @see #setCurrentPosition(Position)
	 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getSwitch_CurrentPosition()
	 * @model unique="false"
	 * @generated
	 */
	Position getCurrentPosition();

	/**
	 * Sets the value of the '{@link hu.bme.mit.trainbenchmark.railway.Switch#getCurrentPosition <em>Current Position</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Current Position</em>' attribute.
	 * @see hu.bme.mit.trainbenchmark.railway.Position
	 * @see #getCurrentPosition()
	 * @generated
	 */
	void setCurrentPosition(Position value);

	/**
	 * Returns the value of the '<em><b>Positions</b></em>' reference list.
	 * The list contents are of type {@link hu.bme.mit.trainbenchmark.railway.SwitchPosition}.
	 * It is bidirectional and its opposite is '{@link hu.bme.mit.trainbenchmark.railway.SwitchPosition#getTarget <em>Target</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Positions</em>' reference list.
	 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getSwitch_Positions()
	 * @see hu.bme.mit.trainbenchmark.railway.SwitchPosition#getTarget
	 * @model opposite="target"
	 * @generated
	 */
	EList<SwitchPosition> getPositions();

} // Switch
