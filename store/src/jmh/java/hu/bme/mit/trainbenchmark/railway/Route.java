/**
 */
package hu.bme.mit.trainbenchmark.railway;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Route</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link hu.bme.mit.trainbenchmark.railway.Route#isActive <em>Active</em>}</li>
 *   <li>{@link hu.bme.mit.trainbenchmark.railway.Route#getFollows <em>Follows</em>}</li>
 *   <li>{@link hu.bme.mit.trainbenchmark.railway.Route#getRequires <em>Requires</em>}</li>
 *   <li>{@link hu.bme.mit.trainbenchmark.railway.Route#getEntry <em>Entry</em>}</li>
 *   <li>{@link hu.bme.mit.trainbenchmark.railway.Route#getExit <em>Exit</em>}</li>
 * </ul>
 *
 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getRoute()
 * @model
 * @generated
 */
public interface Route extends RailwayElement {
	/**
	 * Returns the value of the '<em><b>Active</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Active</em>' attribute.
	 * @see #setActive(boolean)
	 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getRoute_Active()
	 * @model unique="false"
	 * @generated
	 */
	boolean isActive();

	/**
	 * Sets the value of the '{@link hu.bme.mit.trainbenchmark.railway.Route#isActive <em>Active</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Active</em>' attribute.
	 * @see #isActive()
	 * @generated
	 */
	void setActive(boolean value);

	/**
	 * Returns the value of the '<em><b>Follows</b></em>' containment reference list.
	 * The list contents are of type {@link hu.bme.mit.trainbenchmark.railway.SwitchPosition}.
	 * It is bidirectional and its opposite is '{@link hu.bme.mit.trainbenchmark.railway.SwitchPosition#getRoute <em>Route</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Follows</em>' containment reference list.
	 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getRoute_Follows()
	 * @see hu.bme.mit.trainbenchmark.railway.SwitchPosition#getRoute
	 * @model opposite="route" containment="true"
	 * @generated
	 */
	EList<SwitchPosition> getFollows();

	/**
	 * Returns the value of the '<em><b>Requires</b></em>' reference list.
	 * The list contents are of type {@link hu.bme.mit.trainbenchmark.railway.Sensor}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Requires</em>' reference list.
	 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getRoute_Requires()
	 * @model lower="2"
	 * @generated
	 */
	EList<Sensor> getRequires();

	/**
	 * Returns the value of the '<em><b>Entry</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Entry</em>' reference.
	 * @see #setEntry(Semaphore)
	 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getRoute_Entry()
	 * @model
	 * @generated
	 */
	Semaphore getEntry();

	/**
	 * Sets the value of the '{@link hu.bme.mit.trainbenchmark.railway.Route#getEntry <em>Entry</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Entry</em>' reference.
	 * @see #getEntry()
	 * @generated
	 */
	void setEntry(Semaphore value);

	/**
	 * Returns the value of the '<em><b>Exit</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Exit</em>' reference.
	 * @see #setExit(Semaphore)
	 * @see hu.bme.mit.trainbenchmark.railway.RailwayPackage#getRoute_Exit()
	 * @model
	 * @generated
	 */
	Semaphore getExit();

	/**
	 * Sets the value of the '{@link hu.bme.mit.trainbenchmark.railway.Route#getExit <em>Exit</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Exit</em>' reference.
	 * @see #getExit()
	 * @generated
	 */
	void setExit(Semaphore value);

} // Route
